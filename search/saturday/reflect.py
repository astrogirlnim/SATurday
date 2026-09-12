"""
Plateau / novelty reflection for satday auto (no LLM required).

Progress is defined dynamically: the open Frontier sorry set extracted from
the rung Lean home must shrink. There is no hard-coded pin name list.

When stuck on formalize, default recovery stays on formalize (config-driven)
rather than flipping to prose. Operator force_actions are never overwritten.
"""

from __future__ import annotations

import fcntl
import json
import re
import time
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence

from search.saturday.control import (
    engage_kill,
    load_control,
    pause_rung,
    reflect_path,
    set_force_action,
)


DECL_RE = re.compile(
    r"(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)


@dataclass
class RungReflect:
    """Per-rung plateau counters."""

    last_obligations: List[str] = field(default_factory=list)
    wakes_without_obligation_progress: int = 0
    recent_decl_names: List[str] = field(default_factory=list)
    recent_decl_prefixes: List[str] = field(default_factory=list)
    recent_error_classes: List[str] = field(default_factory=list)
    consecutive_near_duplicates: int = 0
    consecutive_same_error: int = 0
    last_action: str = ""
    last_result: str = ""


@dataclass
class ReflectState:
    """Persisted reflection state across wakes."""

    rungs: Dict[str, RungReflect] = field(default_factory=dict)
    updated_at: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "updated_at": self.updated_at,
            "rungs": {k: asdict(v) for k, v in self.rungs.items()},
        }


@dataclass
class ReflectDecision:
    """Outcome of one reflection pass."""

    action_override: Optional[str] = None
    kill: bool = False
    pause_rung: bool = False
    reject_draft: bool = False
    reason: str = ""
    notes: List[str] = field(default_factory=list)


def _parse_reflect_text(text: str) -> Dict[str, Any]:
    """Parse reflect JSON; tolerate trailing junk from a prior unlocked race."""
    decoder = json.JSONDecoder()
    obj, _end = decoder.raw_decode(text.lstrip())
    if not isinstance(obj, dict):
        raise ValueError("reflect root must be an object")
    return obj


def _state_from_raw(raw: Dict[str, Any]) -> ReflectState:
    state = ReflectState()
    state.updated_at = str(raw.get("updated_at") or "")
    for rid, blob in (raw.get("rungs") or {}).items():
        state.rungs[rid] = RungReflect(
            last_obligations=list(blob.get("last_obligations") or []),
            wakes_without_obligation_progress=int(
                blob.get("wakes_without_obligation_progress") or 0
            ),
            recent_decl_names=list(blob.get("recent_decl_names") or []),
            recent_decl_prefixes=list(blob.get("recent_decl_prefixes") or []),
            recent_error_classes=list(blob.get("recent_error_classes") or []),
            consecutive_near_duplicates=int(
                blob.get("consecutive_near_duplicates") or 0
            ),
            consecutive_same_error=int(blob.get("consecutive_same_error") or 0),
            last_action=str(blob.get("last_action") or ""),
            last_result=str(blob.get("last_result") or ""),
        )
    return state


@contextmanager
def _reflect_file_lock(repo_root: Path) -> Iterator[Path]:
    """
    Exclusive lock around reflect load or modify or save.

    Parallel R2 and R5 workers both update this file; without a lock they
    corrupt JSON and lose each other's counters.
    """
    path = reflect_path(repo_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = path.with_suffix(path.suffix + ".lock")
    print(f"[saturday.reflect] acquiring lock path={lock_path}")
    with lock_path.open("a+", encoding="utf-8") as lock_fh:
        fcntl.flock(lock_fh.fileno(), fcntl.LOCK_EX)
        print(f"[saturday.reflect] lock acquired path={lock_path}")
        try:
            yield path
        finally:
            fcntl.flock(lock_fh.fileno(), fcntl.LOCK_UN)
            print(f"[saturday.reflect] lock released path={lock_path}")


def load_reflect(repo_root: Path) -> ReflectState:
    path = reflect_path(repo_root)
    state = ReflectState()
    if not path.exists():
        return state
    try:
        raw = _parse_reflect_text(path.read_text(encoding="utf-8"))
        state = _state_from_raw(raw)
        print(f"[saturday.reflect] loaded rungs={list(state.rungs)}")
    except (json.JSONDecodeError, OSError, TypeError, ValueError) as exc:
        print(f"[saturday.reflect] bad reflect file: {exc}")
    return state


def save_reflect(repo_root: Path, state: ReflectState) -> None:
    path = reflect_path(repo_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    state.updated_at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    path.write_text(json.dumps(state.to_dict(), indent=2) + "\n", encoding="utf-8")
    print(f"[saturday.reflect] saved path={path}")


def decl_prefix(name: str, parts: int = 4) -> str:
    """Coarse family key: validatesTautologyResult_batch_time_of_* -> first tokens."""
    tokens = [t for t in re.split(r"[_\d]+", name) if t]
    if not tokens:
        return name
    return "_".join(tokens[:parts])


def extract_decl_names(lean_text: str) -> List[str]:
    return DECL_RE.findall(lean_text or "")


def error_class(digest: str) -> str:
    """Normalize lake error digests into coarse classes."""
    text = (digest or "").lower()
    if "ambient" in text and ("red" in text or "build" in text):
        return "ambient_red"
    if "unknown identifier" in text:
        return "unknown_identifier"
    if "type mismatch" in text:
        return "type_mismatch"
    if "linarith" in text:
        return "linarith"
    if "unsolved goals" in text:
        return "unsolved_goals"
    if "formula" in text and "unknown" in text:
        return "unknown_formula"
    if not text.strip():
        return "empty"
    for line in text.splitlines():
        if "error:" in line:
            return re.sub(r"\s+", " ", line)[:120]
    return text[:80]


def is_near_duplicate_name(name: str, recent: Sequence[str]) -> bool:
    pref = decl_prefix(name)
    for old in recent:
        if name == old:
            return True
        if decl_prefix(old) == pref:
            return True
    return False


def draft_is_novel(lean_text: str, recent_names: Sequence[str]) -> tuple[bool, str]:
    names = extract_decl_names(lean_text)
    if not names:
        return True, "no decl names to compare"
    for name in names:
        if is_near_duplicate_name(name, recent_names):
            return False, f"near-duplicate decl family for {name}"
    return True, f"novel decls={names}"


def frontier_progressed(
    prev: Sequence[str], now: Sequence[str]
) -> tuple[bool, str]:
    """True when the open Frontier sorry set strictly shrinks."""
    if not prev:
        return False, "no prior obligation baseline"
    closed = sorted(set(prev) - set(now))
    if closed:
        return True, f"frontier sorries closed: {closed}"
    if set(now) < set(prev):
        return True, "frontier sorry set shrank"
    return False, "frontier sorry set unchanged"


def _apply_plateau_recovery(
    repo_root: Path,
    rung_id: str,
    prefer_switch: str,
    reason: str,
) -> Optional[str]:
    """
    Apply config-driven plateau recovery without clobbering operator force.

    prefer_switch values:
      formalize | prove | falsify | audit — force that action
      clear — drop force so chooser decides
      stay — keep current force / chooser; no write
    """
    action = (prefer_switch or "formalize").strip().lower()
    if action in {"stay", "none", ""}:
        print(f"[saturday.reflect] plateau stay: {reason}")
        return None
    if action == "clear":
        from search.saturday.control import clear_force_action

        clear_force_action(repo_root, rung_id)
        print(f"[saturday.reflect] plateau clear force: {reason}")
        return None
    set_force_action(repo_root, rung_id, action, source="reflect")
    return action


def record_wave_outcome(
    repo_root: Path,
    *,
    rung_id: str,
    action: str,
    result: str,
    obligations_now: Sequence[str],
    applied_decls: Sequence[str],
    reverted: bool,
    error_digest: str,
    cfg: Any,
    ambient_ok: bool = True,
) -> ReflectDecision:
    """
    Update reflect state after one workstream finishes a wake.

    cfg is SaturdayReflectConfig-like (attributes accessed dynamically).
    Load/modify/save runs under an exclusive file lock so parallel workstreams
    cannot corrupt saturday_reflect.json or drop each other's counters.
    """
    decision = ReflectDecision()
    notes: List[str] = []

    max_no_progress = int(getattr(cfg, "max_wakes_without_obligation_progress", 5))
    max_dupes = int(getattr(cfg, "max_consecutive_near_duplicates", 3))
    max_same_err = int(getattr(cfg, "max_consecutive_same_error", 3))
    auto_kill = bool(getattr(cfg, "auto_kill_on_plateau", True))
    prefer_switch = str(getattr(cfg, "plateau_switch_action", "formalize"))

    with _reflect_file_lock(repo_root):
        state = load_reflect(repo_root)
        row = state.rungs.get(rung_id) or RungReflect()

        prev = list(row.last_obligations)
        now = list(obligations_now)
        progressed, prog_note = frontier_progressed(prev, now)
        if progressed:
            notes.append(prog_note)

        # Ambient lake red is infrastructure, not a formalize strategy failure.
        if not ambient_ok:
            notes.append("ambient lake red; skip no-progress increment")
            print(f"[saturday.reflect] ambient red on {rung_id}; not counting plateau")
        elif action == "formalize" and not progressed:
            row.wakes_without_obligation_progress += 1
        elif progressed:
            row.wakes_without_obligation_progress = 0

        for name in applied_decls:
            row.recent_decl_names = (row.recent_decl_names + [name])[-40:]
            pref = decl_prefix(name)
            row.recent_decl_prefixes = (row.recent_decl_prefixes + [pref])[-40:]

        ec = error_class(error_digest)
        if (reverted or result == "partial") and ambient_ok and ec not in {
            "empty",
            "ambient_red",
        }:
            if row.recent_error_classes and row.recent_error_classes[-1] == ec:
                row.consecutive_same_error += 1
            else:
                row.consecutive_same_error = 1
            row.recent_error_classes = (row.recent_error_classes + [ec])[-20:]
            notes.append(f"error_class={ec} streak={row.consecutive_same_error}")
        elif progressed or not ambient_ok:
            if not ambient_ok:
                row.consecutive_same_error = 0

        if applied_decls and not progressed:
            if any(
                is_near_duplicate_name(n, row.recent_decl_names[:-1])
                for n in applied_decls
            ):
                row.consecutive_near_duplicates += 1
                notes.append(
                    f"near-duplicate helper streak={row.consecutive_near_duplicates}"
                )
            else:
                row.consecutive_near_duplicates = 0
        elif progressed:
            row.consecutive_near_duplicates = 0

        row.last_obligations = now
        row.last_action = action
        row.last_result = result
        state.rungs[rung_id] = row
        save_reflect(repo_root, state)

    if row.wakes_without_obligation_progress >= max_no_progress:
        override = _apply_plateau_recovery(
            repo_root,
            rung_id,
            prefer_switch,
            f"{rung_id}: {row.wakes_without_obligation_progress} formalize wakes "
            f"without Frontier sorry progress",
        )
        decision.action_override = override
        decision.reason = (
            f"{rung_id}: {row.wakes_without_obligation_progress} formalize wakes "
            f"without Frontier sorry progress; recovery={prefer_switch}"
        )
        notes.append(decision.reason)

    if row.consecutive_near_duplicates >= max_dupes:
        override = _apply_plateau_recovery(
            repo_root,
            rung_id,
            prefer_switch,
            f"{rung_id}: near-duplicate helper families",
        )
        decision.action_override = override or decision.action_override
        decision.reason = (
            f"{rung_id}: {row.consecutive_near_duplicates} near-duplicate helper "
            f"families; recovery={prefer_switch}"
        )
        notes.append(decision.reason)

    if row.consecutive_same_error >= max_same_err:
        decision.pause_rung = True
        decision.action_override = "audit"
        decision.reason = (
            f"{rung_id}: same error class {max_same_err} times; pause formalize, audit"
        )
        pause_rung(repo_root, rung_id, decision.reason)
        set_force_action(repo_root, rung_id, "audit", source="reflect")
        notes.append(decision.reason)
        if auto_kill and row.wakes_without_obligation_progress >= max_no_progress:
            decision.kill = True
            engage_kill(repo_root, decision.reason, source="reflect")
            notes.append("auto kill engaged")

    # Hard kill only when recovery is not "keep formalizing".
    kill_on_formalize_hold = prefer_switch not in {
        "formalize",
        "stay",
        "none",
        "clear",
        "",
    }
    if (
        auto_kill
        and kill_on_formalize_hold
        and row.wakes_without_obligation_progress >= max_no_progress + 2
    ):
        decision.kill = True
        decision.reason = (
            f"{rung_id}: plateau beyond {max_no_progress + 2} wakes; kill auto loop"
        )
        engage_kill(repo_root, decision.reason, source="reflect")
        notes.append(decision.reason)

    decision.notes = notes
    print(
        f"[saturday.reflect] rung={rung_id} decision kill={decision.kill} "
        f"override={decision.action_override} reason={decision.reason!r}"
    )
    return decision


def suggest_action_override(repo_root: Path, rung_id: str) -> Optional[str]:
    """Chooser hook: honor control.force_actions if set."""
    ctrl = load_control(repo_root)
    if rung_id in ctrl.paused_rungs and rung_id not in ctrl.force_actions:
        print(f"[saturday.reflect] rung {rung_id} paused; defaulting to audit")
        return "audit"
    forced = ctrl.force_actions.get(rung_id)
    if forced:
        src = ctrl.force_action_sources.get(rung_id, "")
        print(f"[saturday.reflect] force_action {rung_id} -> {forced} (src={src})")
    return forced


# Back-compat alias for older imports; always empty (pins are dynamic).
CRITICAL_PINS: Dict[str, List[str]] = {}


def open_critical_pins(obligations: Sequence[str], rung_id: str = "") -> List[str]:
    """All open Frontier obligations count as the live pin list (dynamic)."""
    _ = rung_id
    return list(obligations)
