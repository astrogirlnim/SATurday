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
# Off-target R2 drafts that reinvent completed graft/width substitution
R2_OFF_TARGET_RE = re.compile(
    r"d\.width\s*≤\s*max\s+W\s+dG\.width|exists_derivation_graft_width|"
    r"derivation_width_after_substitution|width_substitution_bound|"
    r"width_after_substitution",
    re.IGNORECASE,
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
    subprocess.run(
        ["find", ".", "-name", "._*", "-not", "-path", "./.lake/*", "-delete"],
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
    """Prefer real Lean error lines over trailing mathlib dirty warnings."""
    lines = output.splitlines()
    useful = [
        ln
        for ln in lines
        if ("error:" in ln.lower())
        or ("unexpected token" in ln.lower())
        or ("unknown identifier" in ln.lower())
        or ("failed to synthesize" in ln.lower())
        or ln.strip().startswith("warning: Theory/")
    ]
    if useful:
        digest = "\n".join(useful[:60])
        return digest[-limit:]
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
    if AXIOM_RE.search(text):
        return None, "draft declares axiom (forbidden)"
    if LEAN3_BEGIN_RE.search(text):
        return None, "draft still looks like Lean 3 after begin/end rewrite"
    if LEAN3_RANGE_RE.search(text):
        return None, "draft uses Lean 3 range syntax [a..b]; use List.range or Finset.range"

    if rung_id == "r2-width-machinery" and R2_OFF_TARGET_RE.search(text):
        if "exists_cs_clause_expanding" not in text and "exists_spreads_matchable" not in text:
            return None, (
                "off-target R2 draft (width graft already certified). "
                "Target CSExpansionFrontier.exists_cs_clause_expanding_3cnf "
                "or exists_spreads_matchable_unsat_random3CNF"
            )

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
    """Insert fragment before the module outer end line when possible."""
    end_marker = OUTER_END_BY_RUNG.get(rung_id)
    block = "\n\n" + fragment.rstrip() + "\n"
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
    """Map decl name -> full theorem/lemma block text (best effort)."""
    matches = list(
        re.finditer(r"(?m)^(?:/--[\s\S]*?-/)\s*|^(?:theorem|lemma)\s+", body)
    )
    # Find theorem/lemma starts only
    starts = [
        m.start()
        for m in re.finditer(r"(?m)^(?:theorem|lemma)\s+[A-Za-z0-9_']+", body)
    ]
    # Include preceding doc comment if any
    blocks: dict[str, str] = {}
    for i, start in enumerate(starts):
        # back up over optional /-- ... -/
        doc_start = start
        prefix = body[:start]
        doc = re.search(r"(?ms)(/--.*?-/)\s*\Z", prefix)
        if doc:
            doc_start = doc.start(1)
        end = starts[i + 1] if i + 1 < len(starts) else len(body)
        chunk = body[doc_start:end].strip()
        name_m = re.match(
            r"(?ms)(?:/--.*?-/\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)", chunk
        )
        if name_m:
            blocks[name_m.group(1)] = chunk
    return blocks


def _replace_decl(source: str, name: str, new_block: str) -> str:
    """Replace an existing theorem/lemma block by name."""
    pattern = re.compile(
        rf"(?ms)(?:/--.*?-/\s*)?(?:theorem|lemma)\s+{re.escape(name)}\b.*?"
        rf"(?=(?:/--.*?-/\s*)?(?:theorem|lemma)\s+|\nnamespace |\nend |\Z)"
    )
    new_source, n = pattern.subn(new_block.rstrip() + "\n\n", source, count=1)
    if n != 1:
        raise ValueError(f"failed to replace decl {name} (matches={n})")
    return new_source


def merge_frontier_fragment(original: str, fragment: str, rung_id: str) -> tuple[str, str]:
    """
    Merge fragment into original by inserting new Frontier decls only.

    In-place sorry replacement is disabled until we have a non-greedy Lean
    parser; a prior regex replace truncated Bridge/ProofSystem.lean.
    """
    open_sorry = set(extract_open_frontier_obligations(original))
    incoming = _existing_decl_names(fragment)
    existing = _existing_decl_names(original)
    dupes = sorted(existing & incoming)
    if dupes:
        open_dupes = [n for n in dupes if n in open_sorry]
        hard = [n for n in dupes if n not in open_sorry]
        if hard:
            raise ValueError(
                "decls already defined (certified): " + ", ".join(hard[:12])
            )
        raise ValueError(
            "decls already defined as open Frontier sorry: "
            + ", ".join(open_dupes[:12])
            + ". Emit a NEW helper lemma name (in-place sorry replace is disabled)."
        )

    updated = insert_fragment(original, fragment, rung_id)
    return updated, "insert=" + ",".join(sorted(incoming))


def apply_frontier_draft(
    repo_root: Path,
    lean_path: Path,
    lean_code: str,
    rung_id: str,
) -> ApplyResult:
    """
    Auto-apply a Frontier draft into lean_path if lake build stays green.

    On build failure, restore the previous file contents.
    """
    repo_root = Path(repo_root)
    lean_path = Path(lean_path)
    try:
        rel = str(lean_path.relative_to(repo_root))
    except ValueError:
        rel = str(lean_path)
    print(f"[saturday.apply] start target={rel} rung={rung_id}")
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
            updated, mode = merge_frontier_fragment(backup, fragment, rung_id)
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
