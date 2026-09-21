"""
Auto-apply formalize drafts into theory/ under Frontier quarantine.

Safety rules:
- Only Frontier namespaces (name contains Frontier)
- No axiom commands
- Rewrite Lean 3 begin/end; reject leftover Lean 3 syntax
- Existing certified decls cannot be redefined
- Open Frontier sorry decls MAY be replaced in place
- Backup target file; lake build must pass; revert on failure
- Entire write/build/revert is globally serialized across workstreams
"""

from __future__ import annotations

import re
import threading
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from search.saturday.ui import announce

_THEORY_LOCK = threading.RLock()

LEAN3_BEGIN_RE = re.compile(r"(?m)(?::=\s*begin\b|^\s*begin\s*$)")
LEAN3_PROOF_BLOCK_RE = re.compile(
    r":=\s*begin\b(.*?)^\s*end\s*$",
    re.MULTILINE | re.DOTALL,
)
LEAN3_RANGE_RE = re.compile(r"\[\s*[^\]]*\.\.[^\]]*\]")
# Model often appends status JSON inside a Lean block comment
TRAILING_STATUS_JSON_RE = re.compile(
    r"(?ms)/\-\s*\{[^{}]*\"status\"[^{}]*\}\s*\-/\s*\Z"
)
AXIOM_RE = re.compile(r"(?m)^\s*axiom\s+")
NAMESPACE_RE = re.compile(r"(?m)^\s*namespace\s+(\S+)")
THEOREM_NAME_RE = re.compile(
    r"(?m)^\s*(?:theorem|lemma|def|structure|inductive|class)\s+([A-Za-z0-9_']+)"
)
# theorem/lemma name ... := by sorry without crossing another decl header
OPEN_SORRY_DECL_RE = re.compile(
    r"(?ms)^\s*(theorem|lemma)\s+([A-Za-z0-9_']+)\b"
    r"(?:(?!^\s*(?:theorem|lemma|namespace|end)\s).)*?"
    r":=\s*by\s+sorry\b"
)
OUTER_END_BY_RUNG = {
    "r2-width-machinery": "end SATurday.ProofComplexity",
    "r5-cook-reckhow-bridge": "end SATurday.Bridge",
    "r0-resolution-foundations": "end SATurday.ProofComplexity",
    "r1-php-haken": "end SATurday.ProofComplexity",
}

DEFAULT_FRONTIER_NS = {
    "r2-width-machinery": "CSExpansionFrontier",
    "r5-cook-reckhow-bridge": "ProofSystemFrontier",
}


@dataclass
class ApplyResult:
    """Outcome of attempting to auto-apply a Lean draft."""

    applied: bool
    reverted: bool
    build_ok: bool
    target: str
    notes: str
    has_sorry: bool = False
    build_tail: str = ""


def _lake_build_unlocked(repo_root: Path) -> dict:
    """Run lake build. Caller must hold _THEORY_LOCK."""
    import subprocess

    theory = repo_root / "theory"
    print(f"[saturday.apply] lake build in {theory}")
    # macOS AppleDouble sidecar files break lake UTF-8 reads (._Foo.lean)
    subprocess.run(
        ["find", ".", "-name", "._*", "-delete"],
        cwd=str(theory),
        capture_output=True,
        text=True,
        check=False,
    )
    proc = subprocess.run(
        ["lake", "build"],
        cwd=str(theory),
        capture_output=True,
        text=True,
        check=False,
    )
    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    ok = proc.returncode == 0
    print(f"[saturday.apply] lake build ok={ok} exit={proc.returncode}")
    return {"ok": ok, "output": output, "returncode": proc.returncode}


def lake_build_locked(repo_root: Path) -> dict:
    """Serialize lake build across parallel workstreams."""
    print(f"[saturday.apply] lake build (locked) in {repo_root / 'theory'}")
    with _THEORY_LOCK:
        return _lake_build_unlocked(repo_root)


def build_error_digest(output: str, limit: int = 2500) -> str:
    """
    Prefer real Lean errors over noise.

    Ignores unused-simp / style warnings and mathlib 'local changes' spam so
    OpenRouter escalate prompts get actionable failures.
    """
    lines = output.splitlines()
    noise_substrings = (
        "this simp argument is unused",
        "try 'simp' instead of 'simpa'",
        "where `(tac1; tac2)` would suffice",
        "'omega' tactic does nothing",
        "has local changes",
        "declaration uses `sorry`",
    )

    def is_noise(ln: str) -> bool:
        low = ln.lower()
        return any(s in low for s in noise_substrings)

    errors = [
        ln
        for ln in lines
        if (
            ln.strip().lower().startswith("error:")
            or "error:" in ln.lower()
            or "unexpected token" in ln.lower()
            or "unknown identifier" in ln.lower()
            or "failed to synthesize" in ln.lower()
            or "type mismatch" in ln.lower()
            or "unsolved goals" in ln.lower()
            or "invalid field" in ln.lower()
            or "failed to compile" in ln.lower()
            or "lean exited with code" in ln.lower()
        )
        and not is_noise(ln)
    ]
    if errors:
        digest = "\n".join(errors[:80])
        return digest[-limit:]

    # Fallback: Theory/ warnings that are not style noise, then raw tail
    theory_warns = [
        ln
        for ln in lines
        if ln.strip().startswith("warning: Theory/") and not is_noise(ln)
    ]
    if theory_warns:
        digest = "\n".join(theory_warns[:40])
        return digest[-limit:]

    # Last non-empty lines excluding mathlib package dirty spam
    tail = [
        ln
        for ln in lines
        if ln.strip()
        and "has local changes" not in ln.lower()
        and not is_noise(ln)
    ]
    if tail:
        return "\n".join(tail[-60:])[-limit:]
    return output[-limit:]


def extract_open_frontier_obligations(source: str) -> list[str]:
    """Names of theorem/lemma decls whose proof is currently `sorry`."""
    names = [m.group(2) for m in OPEN_SORRY_DECL_RE.finditer(source)]
    # stable unique order
    seen = set()
    out = []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def rewrite_lean3_begin_end(text: str) -> str:
    """Rewrite Lean 3 `:= begin ... end` proof bodies to Lean 4 `:= by ...`."""
    rewritten, n = LEAN3_PROOF_BLOCK_RE.subn(r":= by\1", text)
    if n:
        print(f"[saturday.apply] rewrote {n} Lean 3 begin/end proof block(s) to by")
    return rewritten


def prepare_frontier_fragment(lean_code: str, rung_id: str) -> tuple[Optional[str], str]:
    """
    Validate and normalize a draft into a Frontier-only fragment.

    Returns (fragment_or_none, reason).
    """
    text = lean_code.strip()
    if not text:
        return None, "empty draft"
    lines = []
    for line in text.splitlines():
        if line.strip().startswith("import "):
            print(f"[saturday.apply] drop import line: {line.strip()}")
            continue
        lines.append(line)
    text = "\n".join(lines).strip()
    text = rewrite_lean3_begin_end(text)
    text, n_json = TRAILING_STATUS_JSON_RE.subn("", text)
    if n_json:
        print("[saturday.apply] stripped trailing model status JSON comment")
        text = text.strip()
    if AXIOM_RE.search(text):
        return None, "draft declares axiom (forbidden)"
    if LEAN3_BEGIN_RE.search(text):
        return None, "draft still looks like Lean 3 after begin/end rewrite"
    if LEAN3_RANGE_RE.search(text):
        return None, "draft uses Lean 3 range syntax [a..b]; use List.range or Finset.range"

    namespaces = NAMESPACE_RE.findall(text)
    if namespaces:
        if not any("Frontier" in ns for ns in namespaces):
            return None, f"namespace lacks Frontier marker: {namespaces}"
    else:
        ns = DEFAULT_FRONTIER_NS.get(rung_id, "LocalDraftFrontier")
        print(f"[saturday.apply] wrapping draft in namespace {ns}")
        text = f"namespace {ns}\n\n{text}\n\nend {ns}"

    expected_ns = DEFAULT_FRONTIER_NS.get(rung_id)
    if expected_ns:
        for ns in NAMESPACE_RE.findall(text):
            if "Frontier" in ns and ns != expected_ns:
                print(f"[saturday.apply] remap namespace {ns} -> {expected_ns}")
                text = text.replace(f"namespace {ns}", f"namespace {expected_ns}")
                text = text.replace(f"end {ns}", f"end {expected_ns}")

    namespaces = NAMESPACE_RE.findall(text)
    if not any("Frontier" in ns for ns in namespaces):
        return None, "failed to establish Frontier namespace"

    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    header = f"/- SATurday auto-apply {stamp} (rung {rung_id}). -/\n"
    return header + text + "\n", "ok"


def insert_fragment(original: str, fragment: str, rung_id: str) -> str:
    """
    Insert fragment after the last Frontier namespace close when possible.

    Inserting only before the module `end` can land inside an open Frontier
    block if a prior auto-apply left nesting ambiguous; prefer after
    `end CSExpansionFrontier` / `end ProofSystemFrontier`.
    """
    frontier_end = {
        "r2-width-machinery": "end CSExpansionFrontier",
        "r5-cook-reckhow-bridge": "end ProofSystemFrontier",
    }.get(rung_id)
    # R2 also owns MGGFrontier in MGG.lean; prefer the Frontier end that
    # actually appears in this file (and matches the draft namespace).
    candidates = []
    if "MGGFrontier" in fragment or "end MGGFrontier" in original:
        candidates.append("end MGGFrontier")
    if frontier_end:
        candidates.append(frontier_end)
    if "end ProofSystemFrontier" in original:
        candidates.append("end ProofSystemFrontier")
    end_marker = OUTER_END_BY_RUNG.get(rung_id)
    block = "\n\n" + fragment.rstrip() + "\n"
    for fe in candidates:
        if fe and fe in original:
            idx = original.rfind(fe)
            insert_at = idx + len(fe)
            print(
                f"[saturday.apply] insert after {fe!r} at idx={insert_at}"
            )
            return original[:insert_at] + block + original[insert_at:]
    if end_marker and end_marker in original:
        idx = original.rfind(end_marker)
        print(f"[saturday.apply] insert before {end_marker!r} at idx={idx}")
        return original[:idx] + block + "\n" + original[idx:]
    print("[saturday.apply] append at end of file")
    if not original.endswith("\n"):
        original += "\n"
    return original + block


def _existing_decl_names(source: str) -> set[str]:
    """Collect top level theorem/lemma/def names already in a Lean file."""
    return set(THEOREM_NAME_RE.findall(source))


def _strip_ns_wrapper(fragment: str) -> str:
    """Remove outer namespace/end and auto-apply header comments."""
    text = fragment.strip()
    text = re.sub(r"(?m)^/- SATurday auto-apply.*?-/\s*", "", text)
    text = re.sub(r"(?m)^namespace \S+\s*", "", text, count=1)
    text = re.sub(r"(?m)^end \S+\s*$", "", text)
    return text.strip()


def _split_decl_blocks(body: str) -> dict[str, str]:
    """Map decl name -> full theorem/lemma/def block text (best effort)."""
    starts = [
        m.start()
        for m in re.finditer(
            r"(?m)^(?:theorem|lemma|def|abbrev)\s+[A-Za-z0-9_']+", body
        )
    ]
    blocks: dict[str, str] = {}
    for i, start in enumerate(starts):
        # Bounded lookback only: whole-file /--.*?-/ with DOTALL can swallow 100k+.
        window = body[max(0, start - 4000) : start]
        doc_start = start
        doc = re.search(r"(?ms)(/--(?:(?!-/).)*?-/\s*)\Z", window)
        if doc:
            doc_start = start - len(window) + doc.start(1)
        end = starts[i + 1] if i + 1 < len(starts) else len(body)
        region = body[start:end]
        cut = re.search(r"(?m)^(namespace|end)\s", region)
        if cut:
            end = start + cut.start()
        chunk = body[doc_start:end].strip()
        name_m = re.match(
            r"(?ms)(?:/--(?:(?!-/).)*?-/\s*)?(?:theorem|lemma|def|abbrev)\s+"
            r"([A-Za-z0-9_']+)",
            chunk,
        )
        if name_m:
            blocks[name_m.group(1)] = chunk
    print(
        f"[saturday.apply] split_decl_blocks n={len(blocks)} "
        f"names={sorted(blocks)[:12]}"
    )
    return blocks


def _open_sorry_block_span(source: str, name: str) -> tuple[int, int, str]:
    """Locate one open-sorry theorem/lemma by name; return (start, end, old_text)."""
    for m in OPEN_SORRY_DECL_RE.finditer(source):
        if m.group(2) != name:
            continue
        start = m.start()
        window = source[max(0, start - 4000) : start]
        doc = re.search(r"(?ms)(/--(?:(?!-/).)*?-/\s*)\Z", window)
        if doc:
            start = start - len(window) + doc.start(1)
        end = m.end()
        rest = source[end:]
        nxt = re.search(r"(?m)^(theorem|lemma|def|namespace|end)\s", rest)
        if nxt:
            end = end + nxt.start()
        return start, end, source[start:end]
    raise ValueError(f"open Frontier sorry span not found: {name}")


def _replace_open_sorry_block(source: str, name: str, new_block: str) -> str:
    """
    Replace one open-sorry theorem/lemma using span location (not greedy regex).

    The previous whole-file non-greedy `.*?` replace could truncate large modules.
    """
    start, end, old = _open_sorry_block_span(source, name)
    if not re.search(r":=\s*by\s+sorry\b", old):
        raise ValueError(f"refusing replace of non-open-sorry decl: {name}")
    print(
        f"[saturday.apply] replace open sorry decl={name} "
        f"span=[{start},{end}) chars={end - start}"
    )
    return source[:start] + new_block.rstrip() + "\n\n" + source[end:]



def merge_frontier_fragment(
    original: str,
    fragment: str,
    rung_id: str,
    *,
    allow_helper_only: bool = False,
) -> tuple[str, str]:
    """
    Merge fragment into original.

    Policy (dynamic, no pin-name allowlist):
    - If open Frontier sorries exist, the draft MUST replace at least one by name
      (proof discharge). Helpers may accompany that discharge in the same fragment.
    - Pure helper inserts that leave every open sorry untouched are rejected
      unless allow_helper_only (import ladder micro fill_mode=helper_insert).
    - Certified (non-sorry) decls cannot be redefined.
    """
    open_sorry = set(extract_open_frontier_obligations(original))
    body = _strip_ns_wrapper(fragment)
    incoming_blocks = _split_decl_blocks(body)
    if not incoming_blocks:
        # defs / structures only: fall back to name set
        incoming = _existing_decl_names(fragment)
        if not incoming:
            raise ValueError("fragment has no theorem/lemma decls to merge")
        raise ValueError(
            "fragment decls could not be split into blocks; "
            "emit theorem/lemma/def with := ..."
        )

    existing = _existing_decl_names(original)
    updated = original
    replaced: list[str] = []
    helpers: list[str] = []

    for name, block in incoming_blocks.items():
        if name in open_sorry:
            updated = _replace_open_sorry_block(updated, name, block)
            replaced.append(name)
            continue
        if name in existing:
            raise ValueError(
                "decls already defined (certified): " + name
            )
        if allow_helper_only and re.search(r"\bsorry\b", block):
            raise ValueError(
                f"helper_insert rejects sorry in new decl: {name}"
            )
        helpers.append(name)

    if open_sorry and not replaced:
        if allow_helper_only and helpers:
            print(
                "[saturday.apply] allow_helper_only: inserting helpers without "
                f"Frontier discharge helpers={helpers}"
            )
        else:
            raise ValueError(
                "draft does not discharge any open Frontier sorry. Open: "
                + ", ".join(sorted(open_sorry)[:20])
                + ". Restate one of those names with a real proof (helpers may "
                "accompany it in the same fragment)."
            )

    if helpers:
        helper_blocks = [
            incoming_blocks[n] for n in helpers if n in incoming_blocks
        ]
        helper_body = "\n\n".join(helper_blocks)
        ns = DEFAULT_FRONTIER_NS.get(rung_id, "LocalDraftFrontier")
        helper_frag = (
            f"namespace {ns}\n\n{helper_body}\n\nend {ns}\n"
        )
        updated = insert_fragment(updated, helper_frag, rung_id)

    mode_parts = []
    if replaced:
        mode_parts.append("replace=" + ",".join(sorted(replaced)))
    if helpers:
        mode_parts.append("insert=" + ",".join(sorted(helpers)))
    return updated, ";".join(mode_parts) if mode_parts else "noop"


def apply_frontier_draft(
    repo_root: Path,
    lean_path: Path,
    lean_code: str,
    rung_id: str,
    *,
    allow_helper_only: bool = False,
) -> ApplyResult:
    """
    Auto-apply a Frontier draft into lean_path if lake build stays green.

    On build failure, restore the previous file contents.
    Set allow_helper_only for import-ladder micros (fill_mode=helper_insert).
    """
    repo_root = Path(repo_root)
    lean_path = Path(lean_path)
    try:
        rel = str(lean_path.relative_to(repo_root))
    except ValueError:
        rel = str(lean_path)
    print(
        f"[saturday.apply] start target={rel} rung={rung_id} "
        f"allow_helper_only={allow_helper_only}"
    )
    announce(f"Applying Frontier draft into {rel}")

    fragment, reason = prepare_frontier_fragment(lean_code, rung_id)
    if fragment is None:
        print(f"[saturday.apply] reject: {reason}")
        announce(f"Rejected draft before build: {reason}")
        return ApplyResult(
            applied=False,
            reverted=False,
            build_ok=False,
            target=rel,
            notes=f"auto-apply rejected: {reason}",
            has_sorry="sorry" in lean_code,
        )

    # Plateau novelty gate: reject near-duplicate helper families.
    # Open Frontier obligation names are exempt (discharges are the goal).
    try:
        from infra.config.loader import load_config
        from search.saturday.reflect import draft_is_novel, extract_decl_names, load_reflect

        loop_cfg = load_config(repo_root=repo_root).saturday_loop
        reflect_cfg = getattr(loop_cfg, "reflect", None)
        if reflect_cfg and getattr(reflect_cfg, "reject_near_duplicate_drafts", True):
            open_now = set()
            if lean_path.exists():
                open_now = set(
                    extract_open_frontier_obligations(
                        lean_path.read_text(encoding="utf-8")
                    )
                )
            names = extract_decl_names(fragment)
            helper_names = [n for n in names if n not in open_now]
            state = load_reflect(repo_root)
            row = state.rungs.get(rung_id)
            recent = row.recent_decl_names if row else []
            # Only score novelty on non-obligation helpers
            probe = "\n".join(f"lemma {n} : True := by sorry" for n in helper_names)
            novel, why = draft_is_novel(probe if helper_names else "", recent)
            if not helper_names:
                novel, why = True, "discharge-only draft (open Frontier names)"
            print(f"[saturday.apply] novelty check novel={novel} why={why}")
            if not novel:
                announce(f"Rejected near-duplicate draft: {why}")
                return ApplyResult(
                    applied=False,
                    reverted=False,
                    build_ok=False,
                    target=rel,
                    notes=f"auto-apply rejected: {why}",
                    has_sorry="sorry" in fragment,
                    build_tail=why,
                )
    except Exception as exc:
        print(f"[saturday.apply] novelty check skipped: {exc}")

    if not lean_path.exists():
        return ApplyResult(
            applied=False,
            reverted=False,
            build_ok=False,
            target=rel,
            notes=f"auto-apply target missing: {rel}",
            has_sorry="sorry" in fragment,
        )

    with _THEORY_LOCK:
        backup = lean_path.read_text(encoding="utf-8")
        body_key = fragment.strip()
        if body_key in backup:
            print("[saturday.apply] fragment already present; skip")
            return ApplyResult(
                applied=False,
                reverted=False,
                build_ok=True,
                target=rel,
                notes="auto-apply skipped: identical Frontier fragment already in file",
                has_sorry="sorry" in fragment,
            )

        try:
            updated, mode = merge_frontier_fragment(
                backup,
                fragment,
                rung_id,
                allow_helper_only=allow_helper_only,
            )
        except ValueError as exc:
            print(f"[saturday.apply] reject merge: {exc}")
            announce(f"Rejected draft before build: {exc}")
            return ApplyResult(
                applied=False,
                reverted=False,
                build_ok=False,
                target=rel,
                notes=f"auto-apply rejected: {exc}",
                has_sorry="sorry" in fragment,
            )

        # Guard against catastrophic truncation from bad merges
        backup_lines = backup.count("\n") + 1
        updated_lines = updated.count("\n") + 1
        if updated_lines < int(backup_lines * 0.9):
            msg = (
                f"refusing apply: file would shrink from {backup_lines} to "
                f"{updated_lines} lines"
            )
            print(f"[saturday.apply] {msg}")
            announce(msg)
            return ApplyResult(
                applied=False,
                reverted=False,
                build_ok=False,
                target=rel,
                notes=f"auto-apply rejected: {msg}",
                has_sorry="sorry" in fragment,
            )

        lean_path.write_text(updated, encoding="utf-8")
        print(f"[saturday.apply] wrote candidate bytes={len(updated)} mode={mode}")
        announce(f"Wrote candidate ({mode}); running lake build...")
        build = _lake_build_unlocked(repo_root)
        if not build["ok"]:
            lean_path.write_text(backup, encoding="utf-8")
            print("[saturday.apply] reverted after lake failure")
            digest = build_error_digest(build["output"])
            return ApplyResult(
                applied=False,
                reverted=True,
                build_ok=False,
                target=rel,
                notes=f"auto-apply reverted: lake build failed. Digest: {digest}",
                has_sorry="sorry" in fragment,
                build_tail=digest,
            )

        incoming = _existing_decl_names(fragment)
        has_sorry = "sorry" in fragment
        notes = (
            f"auto-apply succeeded into {rel}. mode={mode}. "
            f"decls={sorted(incoming)[:8]}. frontier_sorry={has_sorry}."
        )
        print(f"[saturday.apply] success {notes}")
        return ApplyResult(
            applied=True,
            reverted=False,
            build_ok=True,
            target=rel,
            notes=notes,
            has_sorry=has_sorry,
        )
