"""
Plateau / novelty reflection for satday auto (no LLM required).

Tracks Frontier obligation progress, draft name novelty, and error classes.
When stuck, forces prove/falsify/audit or engages the kill switch.
"""

from __future__ import annotations

import json
import re
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

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

# Critical open pins: closing these is real progress; helper spam is not.
CRITICAL_PINS: Dict[str, List[str]] = {
    "r2-width-machinery": [
        "exists_spreads_matchable_unsat_random3CNF",
        "exists_cs_clause_expanding_3cnf",
        "exists_cs_expanding_3cnf",
        "cs_expansion_width_lower_bound",
        "boundaryCovered_of_eraseMinimal",
    ],
    "r5-cook-reckhow-bridge": [
        "validatesTautologyResult_computableInPolyTime",
        "truthTable_is_prop_proof_system",
    ],
}


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


def load_reflect(repo_root: Path) -> ReflectState:
    path = reflect_path(repo_root)
    state = ReflectState()
    if not path.exists():
        return state
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
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
    # first error token blob
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


def open_critical_pins(obligations: Sequence[str], rung_id: str) -> List[str]:
    crit = CRITICAL_PINS.get(rung_id, [])
    open_set = set(obligations)
    return [c for c in crit if c in open_set]


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
) -> ReflectDecision:
    """
    Update reflect state after one workstream finishes a wake.

    cfg is SaturdayReflectConfig-like (attributes accessed dynamically).
    """
    state = load_reflect(repo_root)
    row = state.rungs.get(rung_id) or RungReflect()
    decision = ReflectDecision()
    notes: List[str] = []

    max_no_progress = int(getattr(cfg, "max_wakes_without_obligation_progress", 5))
    max_dupes = int(getattr(cfg, "max_consecutive_near_duplicates", 3))
    max_same_err = int(getattr(cfg, "max_consecutive_same_error", 3))
    auto_kill = bool(getattr(cfg, "auto_kill_on_plateau", True))
    prefer_switch = str(getattr(cfg, "plateau_switch_action", "prove"))

    prev = list(row.last_obligations)
    now = list(obligations_now)
    crit_prev = set(open_critical_pins(prev, rung_id)) if prev else None
    crit_now = set(open_critical_pins(now, rung_id))

    progressed = False
    if crit_prev is not None and crit_now < crit_prev:
        progressed = True
        notes.append(f"critical pins closed: {sorted(crit_prev - crit_now)}")
    elif prev and set(now) < set(prev):
        progressed = True
        notes.append("frontier sorry set shrank")

    if action == "formalize" and not progressed:
        row.wakes_without_obligation_progress += 1
    elif progressed:
        row.wakes_without_obligation_progress = 0

    # Novelty tracking for applied or attempted decls
    for name in applied_decls:
        row.recent_decl_names = (row.recent_decl_names + [name])[-40:]
        pref = decl_prefix(name)
        row.recent_decl_prefixes = (row.recent_decl_prefixes + [pref])[-40:]

    if reverted or result == "partial":
        ec = error_class(error_digest)
        if ec and ec != "empty":
            if row.recent_error_classes and row.recent_error_classes[-1] == ec:
                row.consecutive_same_error += 1
            else:
                row.consecutive_same_error = 1
            row.recent_error_classes = (row.recent_error_classes + [ec])[-20:]
            notes.append(f"error_class={ec} streak={row.consecutive_same_error}")

    # Near-duplicate applied helpers that do not close critical pins
    if applied_decls and not progressed:
        if any(is_near_duplicate_name(n, row.recent_decl_names[:-1]) for n in applied_decls):
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

    # Decision policy
    if row.wakes_without_obligation_progress >= max_no_progress:
        decision.action_override = prefer_switch
        decision.reason = (
            f"{rung_id}: {row.wakes_without_obligation_progress} formalize wakes "
            f"without critical/Frontier progress; force {prefer_switch}"
        )
        set_force_action(repo_root, rung_id, prefer_switch)
        notes.append(decision.reason)

    if row.consecutive_near_duplicates >= max_dupes:
        decision.action_override = prefer_switch
        decision.reason = (
            f"{rung_id}: {row.consecutive_near_duplicates} near-duplicate helper "
            f"families; force {prefer_switch}"
        )
        set_force_action(repo_root, rung_id, prefer_switch)
        notes.append(decision.reason)

    if row.consecutive_same_error >= max_same_err:
        decision.pause_rung = True
        decision.action_override = "audit"
        decision.reason = (
            f"{rung_id}: same error class {max_same_err} times; pause formalize, audit"
        )
        pause_rung(repo_root, rung_id, decision.reason)
        set_force_action(repo_root, rung_id, "audit")
        notes.append(decision.reason)
        if auto_kill and row.wakes_without_obligation_progress >= max_no_progress:
            decision.kill = True
            engage_kill(repo_root, decision.reason, source="reflect")
            notes.append("auto kill engaged")

    # Full auto kill when both rungs plateau hard
    if auto_kill and row.wakes_without_obligation_progress >= max_no_progress + 2:
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
        print(f"[saturday.reflect] force_action {rung_id} -> {forced}")
    return forced
