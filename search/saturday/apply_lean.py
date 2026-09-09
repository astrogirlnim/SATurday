"""
Auto-apply formalize drafts into theory/ under Frontier quarantine.

Safety rules:
- Only Frontier namespaces (name contains Frontier)
- No axiom commands
- Reject Lean 3 begin/end tactic blocks
- Reject decls whose names already exist in the target file
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

# One theory mutation / lake build at a time (R2 and R5 share the Lake tree)
_THEORY_LOCK = threading.RLock()

LEAN3_BEGIN_RE = re.compile(r"(?m)(?::=\s*begin\b|^\s*begin\s*$)")
AXIOM_RE = re.compile(r"(?m)^\s*axiom\s+")
NAMESPACE_RE = re.compile(r"(?m)^\s*namespace\s+(\S+)")
THEOREM_NAME_RE = re.compile(
    r"(?m)^\s*(?:theorem|lemma|def|structure|inductive|class)\s+([A-Za-z0-9_']+)"
)

OUTER_END_BY_RUNG = {
    "r2-width-machinery": "end SATurday.ProofComplexity",
    "r5-cook-reckhow-bridge": "end SATurday.Bridge",
    "r0-resolution-foundations": "end SATurday.ProofComplexity",
    "r1-php-haken": "end SATurday.ProofComplexity",
}

DEFAULT_FRONTIER_NS = {
    "r2-width-machinery": "WidthFrontier",
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
    if AXIOM_RE.search(text):
        return None, "draft declares axiom (forbidden)"
    if LEAN3_BEGIN_RE.search(text):
        return None, "draft looks like Lean 3 (begin/end)"

    namespaces = NAMESPACE_RE.findall(text)
    if namespaces:
        if not any("Frontier" in ns for ns in namespaces):
            return None, f"namespace lacks Frontier marker: {namespaces}"
    else:
        ns = DEFAULT_FRONTIER_NS.get(rung_id, "LocalDraftFrontier")
        print(f"[saturday.apply] wrapping draft in namespace {ns}")
        text = f"namespace {ns}\n\n{text}\n\nend {ns}"

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

    fragment, reason = prepare_frontier_fragment(lean_code, rung_id)
    if fragment is None:
        print(f"[saturday.apply] reject: {reason}")
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

        existing = _existing_decl_names(backup)
        incoming = _existing_decl_names(fragment)
        dupes = sorted(existing & incoming)
        if dupes:
            print(f"[saturday.apply] reject duplicate decls: {dupes}")
            return ApplyResult(
                applied=False,
                reverted=False,
                build_ok=False,
                target=rel,
                notes=(
                    "auto-apply rejected: decls already defined in target file: "
                    + ", ".join(dupes[:12])
                    + ". Emit a new lemma name or close an existing sorry in place."
                ),
                has_sorry="sorry" in fragment,
            )

        updated = insert_fragment(backup, fragment, rung_id)
        lean_path.write_text(updated, encoding="utf-8")
        print(f"[saturday.apply] wrote candidate bytes={len(updated)}")
        build = _lake_build_unlocked(repo_root)
        if not build["ok"]:
            lean_path.write_text(backup, encoding="utf-8")
            print("[saturday.apply] reverted after lake failure")
            tail = build["output"][-1200:]
            return ApplyResult(
                applied=False,
                reverted=True,
                build_ok=False,
                target=rel,
                notes=f"auto-apply reverted: lake build failed. Tail: {tail}",
                has_sorry="sorry" in fragment,
                build_tail=tail,
            )

        has_sorry = "sorry" in fragment
        names = sorted(incoming)
        notes = (
            f"auto-apply succeeded into {rel}. "
            f"decls={names[:8]}. "
            f"frontier_sorry={has_sorry}."
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
