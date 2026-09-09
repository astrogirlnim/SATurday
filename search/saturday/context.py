"""
Load ladder context for one saturday cycle.

Existing paths and fields used:
- docs/ladder/ladder.md
- docs/ladder/rungs/<rung-id>.md with Status: line
- search/logs/saturday_sessions.jsonl
- docs/p-vs-np-solve-checklist.md
- docs/p-vs-np-stop-conditions.md
"""

from __future__ import annotations

import json
import re
import subprocess
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional


RUNG_IDS = [
    "r0-resolution-foundations",
    "r1-php-haken",
    "r2-width-machinery",
    "r3-stronger-systems",
    "r4-frontier",
    "r5-cook-reckhow-bridge",
]

STATUS_RE = re.compile(r"^Status:\s*(\S+)", re.MULTILINE)
ACTIVE_LIKE = frozenset({"active", "prose_accepted", "blocked"})

# Serialize session log appends across parallel workstreams
_SESSION_LOCK = threading.Lock()
_RUNG_LOCKS: Dict[str, threading.Lock] = {}
_RUNG_LOCKS_GUARD = threading.Lock()


def _rung_lock(rung_id: str) -> threading.Lock:
    with _RUNG_LOCKS_GUARD:
        if rung_id not in _RUNG_LOCKS:
            _RUNG_LOCKS[rung_id] = threading.Lock()
        return _RUNG_LOCKS[rung_id]


@dataclass
class RungState:
    """Parsed rung memory metadata."""

    rung_id: str
    path: Path
    status: str
    text: str


@dataclass
class CycleContext:
    """Everything Step 0 of the saturday skill loads."""

    repo_root: Path
    ladder_text: str
    rungs: Dict[str, RungState] = field(default_factory=dict)
    last_session: Optional[Dict[str, Any]] = None
    checklist_text: str = ""
    stop_conditions_text: str = ""
    sorry_report: str = ""
    disk_report: str = ""


def _read_text(path: Path) -> str:
    print(f"[saturday.context] read {path}")
    return path.read_text(encoding="utf-8")


def load_cycle_context(repo_root: Path) -> CycleContext:
    """Load ladder, rung memories, last session, checklist, hygiene checks."""
    repo_root = Path(repo_root)
    print(f"[saturday.context] load_cycle_context repo_root={repo_root}")

    ladder_path = repo_root / "docs" / "ladder" / "ladder.md"
    ladder_text = _read_text(ladder_path) if ladder_path.exists() else ""

    rungs: Dict[str, RungState] = {}
    rungs_dir = repo_root / "docs" / "ladder" / "rungs"
    for rung_id in RUNG_IDS:
        path = rungs_dir / f"{rung_id}.md"
        if not path.exists():
            print(f"[saturday.context] missing rung memory: {path}")
            continue
        text = _read_text(path)
        match = STATUS_RE.search(text)
        status = match.group(1).lower() if match else "unknown"
        print(f"[saturday.context] rung={rung_id} status={status}")
        rungs[rung_id] = RungState(rung_id=rung_id, path=path, status=status, text=text)

    sessions_path = repo_root / "search" / "logs" / "saturday_sessions.jsonl"
    last_session = None
    if sessions_path.exists():
        lines = [
            line for line in sessions_path.read_text(encoding="utf-8").splitlines() if line.strip()
        ]
        if lines:
            try:
                last_session = json.loads(lines[-1])
                print(
                    f"[saturday.context] last_session rung={last_session.get('rung')} "
                    f"action={last_session.get('action_type')} result={last_session.get('result')}"
                )
            except json.JSONDecodeError as exc:
                print(f"[saturday.context] last session JSON parse failed: {exc}")

    checklist = repo_root / "docs" / "p-vs-np-solve-checklist.md"
    stops = repo_root / "docs" / "p-vs-np-stop-conditions.md"

    sorry_report = _run_sorry_inventory(repo_root)
    disk_report = _run_disk_check(repo_root)

    return CycleContext(
        repo_root=repo_root,
        ladder_text=ladder_text,
        rungs=rungs,
        last_session=last_session,
        checklist_text=_read_text(checklist) if checklist.exists() else "",
        stop_conditions_text=_read_text(stops) if stops.exists() else "",
        sorry_report=sorry_report,
        disk_report=disk_report,
    )


def _run_sorry_inventory(repo_root: Path) -> str:
    """Accepted tree sorry scan (Frontier excluded)."""
    theory = repo_root / "theory"
    print(f"[saturday.context] sorry inventory under {theory}")
    try:
        rg = subprocess.run(
            ["rg", "-n", "sorry", "--glob", "*.lean", "Theory/"],
            cwd=str(theory),
            capture_output=True,
            text=True,
            check=False,
        )
        lines = [ln for ln in rg.stdout.splitlines() if "Frontier" not in ln]
        if not lines:
            report = "accepted tree clean"
        else:
            report = "\n".join(lines[:80])
        print(f"[saturday.context] sorry report lines={0 if not lines else len(lines)}")
        return report
    except FileNotFoundError:
        print("[saturday.context] rg not found; sorry inventory skipped")
        return "rg not found; sorry inventory skipped"


def _run_disk_check(repo_root: Path) -> str:
    """df -h one liner for the workspace volume."""
    print(f"[saturday.context] disk check for {repo_root}")
    try:
        proc = subprocess.run(
            ["df", "-h", str(repo_root)],
            capture_output=True,
            text=True,
            check=False,
        )
        lines = proc.stdout.strip().splitlines()
        report = lines[1] if len(lines) >= 2 else proc.stdout.strip()
        print(f"[saturday.context] disk: {report}")
        return report
    except OSError as exc:
        print(f"[saturday.context] disk check failed: {exc}")
        return f"disk check failed: {exc}"


def append_rung_memory(rung: RungState, entry: str) -> None:
    """Append one dated session log entry; never rewrite history."""
    lock = _rung_lock(rung.rung_id)
    with lock:
        print(f"[saturday.context] append rung memory path={rung.path}")
        # Re-read to avoid stomping a parallel writer on another process
        text = rung.path.read_text(encoding="utf-8") if rung.path.exists() else rung.text
        marker = "## Session log (append-only)"
        block = f"\n{entry.rstrip()}\n"
        if marker in text:
            if not text.endswith("\n"):
                text += "\n"
            text += block
        else:
            text += f"\n{marker}\n{block}"
        rung.path.write_text(text, encoding="utf-8")
        rung.text = text
        print(f"[saturday.context] rung memory updated bytes={len(text)}")


def append_session_record(repo_root: Path, record: Dict[str, Any], sessions_path: str) -> Path:
    """Append exactly one JSON line to saturday_sessions.jsonl."""
    path = repo_root / sessions_path
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(record, ensure_ascii=True)
    with _SESSION_LOCK:
        print(f"[saturday.context] append session record path={path}")
        with path.open("a", encoding="utf-8") as handle:
            handle.write(line + "\n")
    return path


def truncate_for_prompt(text: str, max_chars: int) -> str:
    """Keep prompts within local model context budgets."""
    if len(text) <= max_chars:
        return text
    head = max_chars // 2
    tail = max_chars - head - 80
    return text[:head] + "\n\n...[truncated]...\n\n" + text[-tail:]
