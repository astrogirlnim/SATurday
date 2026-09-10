"""
Live loop heartbeat for the dashboard.

Auto writes search/logs/saturday_live.json on each announce / phase change.
Dashboard reads it so operators see wake progress, not only static pin %.
"""

from __future__ import annotations

import json
import os
import time
from collections import deque
from pathlib import Path
from threading import Lock
from typing import Any, Deque, Dict, List, Optional


LIVE_REL = Path("search/logs/saturday_live.json")
_LOCK = Lock()
_EVENTS: Deque[Dict[str, Any]] = deque(maxlen=80)
_STATE: Dict[str, Any] = {
    "running": False,
    "pid": None,
    "wake": 0,
    "phase": "idle",
    "detail": "",
    "workstreams": {},
    "stats": {
        "wakes": 0,
        "accepted": 0,
        "reverted": 0,
        "rejected": 0,
        "prove": 0,
        "formalize": 0,
        "falsify": 0,
        "audit": 0,
    },
    "models": {},
    "updated_at": "",
}


def live_path(repo_root: Path) -> Path:
    return Path(repo_root) / LIVE_REL


def _now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _persist(repo_root: Optional[Path] = None) -> None:
    root = Path(repo_root) if repo_root else Path(os.environ.get("SATURDAY_REPO_ROOT", "."))
    # Prefer absolute repo from state if set
    if _STATE.get("repo_root"):
        root = Path(str(_STATE["repo_root"]))
    path = live_path(root)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        **_STATE,
        "events": list(_EVENTS),
        "updated_at": _now(),
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def configure_live(repo_root: Path) -> None:
    with _LOCK:
        _STATE["repo_root"] = str(Path(repo_root))
        _STATE["running"] = True
        _STATE["pid"] = os.getpid()
        _STATE["phase"] = "starting"
        _STATE["detail"] = "auto loop starting"
        _STATE["updated_at"] = _now()
        _persist(repo_root)
    print(f"[saturday.live] configured repo={repo_root} pid={os.getpid()}")


def set_phase(phase: str, detail: str = "", *, workstream: Optional[str] = None) -> None:
    with _LOCK:
        _STATE["phase"] = phase
        _STATE["detail"] = detail
        _STATE["updated_at"] = _now()
        if workstream:
            ws = dict(_STATE.get("workstreams") or {})
            ws[workstream] = {"phase": phase, "detail": detail, "at": _now()}
            _STATE["workstreams"] = ws
        _EVENTS.appendleft(
            {"ts": _now(), "kind": "phase", "phase": phase, "detail": detail, "workstream": workstream}
        )
        _persist()


def set_wake(wake: int) -> None:
    with _LOCK:
        _STATE["wake"] = wake
        _STATE["stats"]["wakes"] = max(int(_STATE["stats"].get("wakes") or 0), wake)
        _STATE["phase"] = "wake"
        _STATE["detail"] = f"Wake {wake} starting"
        _STATE["updated_at"] = _now()
        _EVENTS.appendleft({"ts": _now(), "kind": "wake", "wake": wake, "detail": f"Wake {wake}"})
        _persist()


def bump_stat(key: str, n: int = 1) -> None:
    with _LOCK:
        stats = dict(_STATE.get("stats") or {})
        stats[key] = int(stats.get(key) or 0) + n
        _STATE["stats"] = stats
        _STATE["updated_at"] = _now()
        _persist()


def set_models(models: Dict[str, str]) -> None:
    with _LOCK:
        _STATE["models"] = dict(models)
        _STATE["updated_at"] = _now()
        _persist()


def push_event(message: str, *, kind: str = "status", workstream: Optional[str] = None) -> None:
    """Record a human status line for the dashboard feed."""
    text = (message or "").strip()
    if not text:
        return
    with _LOCK:
        _STATE["detail"] = text
        _STATE["updated_at"] = _now()
        # Infer accept/revert from announce text
        low = text.lower()
        if "lean accepted" in low or "auto-apply succeeded" in low:
            _STATE["stats"]["accepted"] = int(_STATE["stats"].get("accepted") or 0) + 1
        if "reverted" in low or "did not compile" in low:
            _STATE["stats"]["reverted"] = int(_STATE["stats"].get("reverted") or 0) + 1
        if "rejected" in low:
            _STATE["stats"]["rejected"] = int(_STATE["stats"].get("rejected") or 0) + 1
        _EVENTS.appendleft(
            {"ts": _now(), "kind": kind, "detail": text, "workstream": workstream}
        )
        _persist()


def mark_stopped(reason: str = "stopped") -> None:
    with _LOCK:
        _STATE["running"] = False
        _STATE["phase"] = "stopped"
        _STATE["detail"] = reason
        _STATE["updated_at"] = _now()
        _EVENTS.appendleft({"ts": _now(), "kind": "stop", "detail": reason})
        _persist()


def load_live(repo_root: Path) -> Dict[str, Any]:
    path = live_path(repo_root)
    if not path.exists():
        return {
            "running": False,
            "phase": "no_live_file",
            "detail": "Auto has not written a live heartbeat yet. Start satday auto --remote.",
            "events": [],
            "stats": {},
            "workstreams": {},
            "wake": 0,
            "models": {},
            "updated_at": "",
        }
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        # Stale if not updated for > 10 minutes while claiming running
        updated = data.get("updated_at") or ""
        data["stale"] = False
        if data.get("running") and updated:
            # cheap staleness: mtime
            age = time.time() - path.stat().st_mtime
            data["stale"] = age > 600
            data["age_seconds"] = int(age)
        return data
    except (json.JSONDecodeError, OSError) as exc:
        print(f"[saturday.live] load failed: {exc}")
        return {"running": False, "phase": "error", "detail": str(exc), "events": []}
