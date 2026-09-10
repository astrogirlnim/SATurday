"""
Manual and automatic kill / pause control for satday auto.

Control file (JSON): search/logs/saturday_control.json
Kill flag (simple): search/logs/saturday_KILL

Dashboard and CLI write these; the auto loop polls them each wake.
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional


CONTROL_REL = Path("search/logs/saturday_control.json")
KILL_FLAG_REL = Path("search/logs/saturday_KILL")
REFLECT_REL = Path("search/logs/saturday_reflect.json")


@dataclass
class ControlState:
    """Operator and reflector control surface."""

    killed: bool = False
    reason: str = ""
    source: str = ""  # manual | reflect | cli | dashboard
    at: str = ""
    paused_rungs: List[str] = field(default_factory=list)
    force_actions: Dict[str, str] = field(default_factory=dict)
    # Per-rung provenance for force_actions: operator | reflect | cli | dashboard
    force_action_sources: Dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


def control_path(repo_root: Path) -> Path:
    return Path(repo_root) / CONTROL_REL


def kill_flag_path(repo_root: Path) -> Path:
    return Path(repo_root) / KILL_FLAG_REL


def reflect_path(repo_root: Path) -> Path:
    return Path(repo_root) / REFLECT_REL


def _now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def load_control(repo_root: Path) -> ControlState:
    """Load control JSON; also honor bare saturday_KILL flag."""
    path = control_path(repo_root)
    flag = kill_flag_path(repo_root)
    state = ControlState()
    if path.exists():
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
            state = ControlState(
                killed=bool(raw.get("killed", False)),
                reason=str(raw.get("reason") or ""),
                source=str(raw.get("source") or ""),
                at=str(raw.get("at") or ""),
                paused_rungs=list(raw.get("paused_rungs") or []),
                force_actions=dict(raw.get("force_actions") or {}),
                force_action_sources=dict(raw.get("force_action_sources") or {}),
            )
            print(
                f"[saturday.control] loaded killed={state.killed} "
                f"paused={state.paused_rungs} force={state.force_actions} "
                f"force_src={state.force_action_sources}"
            )
        except (json.JSONDecodeError, OSError, TypeError) as exc:
            print(f"[saturday.control] bad control file: {exc}")
    if flag.exists() and not state.killed:
        state.killed = True
        state.reason = state.reason or f"kill flag present at {flag}"
        state.source = state.source or "flag"
        state.at = state.at or _now()
        print(f"[saturday.control] kill flag detected path={flag}")
    return state


def save_control(repo_root: Path, state: ControlState) -> Path:
    path = control_path(repo_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state.to_dict(), indent=2) + "\n", encoding="utf-8")
    print(f"[saturday.control] saved path={path} killed={state.killed}")
    return path


def engage_kill(
    repo_root: Path,
    reason: str,
    *,
    source: str = "manual",
) -> ControlState:
    """Stop satday auto on the next wake boundary."""
    state = load_control(repo_root)
    state.killed = True
    state.reason = reason
    state.source = source
    state.at = _now()
    save_control(repo_root, state)
    kill_flag_path(repo_root).write_text(reason + "\n", encoding="utf-8")
    print(f"[saturday.control] KILL engaged source={source} reason={reason!r}")
    return state


def clear_kill(repo_root: Path) -> ControlState:
    """Allow auto to run again."""
    state = load_control(repo_root)
    state.killed = False
    state.reason = ""
    state.source = "unkill"
    state.at = _now()
    save_control(repo_root, state)
    flag = kill_flag_path(repo_root)
    if flag.exists():
        flag.unlink()
        print(f"[saturday.control] removed kill flag {flag}")
    print("[saturday.control] kill cleared")
    return state


def is_killed(repo_root: Path) -> tuple[bool, str]:
    state = load_control(repo_root)
    return state.killed, state.reason


def pause_rung(repo_root: Path, rung_id: str, reason: str = "") -> ControlState:
    state = load_control(repo_root)
    if rung_id not in state.paused_rungs:
        state.paused_rungs.append(rung_id)
    if reason:
        state.reason = reason
    state.at = _now()
    state.source = state.source or "reflect"
    save_control(repo_root, state)
    return state


def set_force_action(
    repo_root: Path,
    rung_id: str,
    action: str,
    *,
    source: str = "reflect",
) -> ControlState:
    """
    Set per-rung forced action.

    Operator-sourced forces are sticky: reflect/cli cannot overwrite them.
    Pass source=\"operator\" (or clear_force_action) to change an operator force.
    """
    state = load_control(repo_root)
    existing_src = str(state.force_action_sources.get(rung_id) or "")
    if existing_src == "operator" and source != "operator":
        print(
            f"[saturday.control] skip force overwrite rung={rung_id} "
            f"kept={state.force_actions.get(rung_id)!r} "
            f"blocked_source={source!r} wanted={action!r}"
        )
        return state
    state.force_actions[rung_id] = action
    state.force_action_sources[rung_id] = source
    state.at = _now()
    if source == "operator":
        state.source = "operator"
    save_control(repo_root, state)
    print(
        f"[saturday.control] force_action rung={rung_id} -> {action!r} "
        f"source={source}"
    )
    return state


def clear_force_action(repo_root: Path, rung_id: str) -> ControlState:
    state = load_control(repo_root)
    state.force_actions.pop(rung_id, None)
    state.force_action_sources.pop(rung_id, None)
    save_control(repo_root, state)
    return state
