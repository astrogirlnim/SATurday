"""
Saturday status report: rung completion and summit readiness toward P vs NP.

Reads authoritative state from:
- docs/ladder/rungs/<id>.md Status lines
- docs/ladder/ladder.md (DAG narrative)
- search/logs/saturday_sessions.jsonl (recent cycles)
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

from search.saturday.chooser import (
    ActionChoice,
    choose_rung_and_action,
    list_parallel_choices,
)
from search.saturday.context import RUNG_IDS, CycleContext, load_cycle_context

RUNG_TITLES = {
    "r0-resolution-foundations": "R0 resolution foundations",
    "r1-php-haken": "R1 PHP Haken lower bound",
    "r2-width-machinery": "R2 width machinery",
    "r3-stronger-systems": "R3 stronger systems",
    "r4-frontier": "R4 open frontier",
    "r5-cook-reckhow-bridge": "R5 Cook Reckhow bridge",
}

MAIN_CLIMB = [
    "r0-resolution-foundations",
    "r1-php-haken",
    "r2-width-machinery",
    "r3-stronger-systems",
    "r4-frontier",
]


@dataclass
class RungStatusRow:
    """One ladder rung row for status output."""

    rung_id: str
    title: str
    status: str
    memory: str


@dataclass
class SummitReadiness:
    """Cook Reckhow summit packaging readiness."""

    r4_certified: bool
    r5_certified: bool
    bridge_open: bool
    summit_ready: bool
    blockers: List[str] = field(default_factory=list)
    summary: str = ""


@dataclass
class SaturdayStatus:
    """Full status payload for CLI or JSON."""

    rungs: List[RungStatusRow]
    counts: Dict[str, int]
    certified: List[str]
    active_work: List[str]
    next_cycle: Dict[str, str]
    parallel_paths: List[Dict[str, str]]
    suggested_commands: List[str]
    summit: SummitReadiness
    last_session: Optional[Dict[str, Any]]
    recent_sessions: List[Dict[str, Any]]
    toward_p_vs_np: str


def _load_recent_sessions(repo_root: Path, limit: int = 5) -> List[Dict[str, Any]]:
    path = repo_root / "search" / "logs" / "saturday_sessions.jsonl"
    print(f"[saturday.status] load sessions path={path} limit={limit}")
    if not path.exists():
        return []
    rows: List[Dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError as exc:
            print(f"[saturday.status] skip bad session line: {exc}")
    return rows[-limit:]


def _summit_readiness(statuses: Dict[str, str]) -> SummitReadiness:
    """Summit needs R4 class hardness plus certified R5 bridge."""
    r4 = statuses.get("r4-frontier", "unknown") == "certified"
    r5 = statuses.get("r5-cook-reckhow-bridge", "unknown") == "certified"
    r1 = statuses.get("r1-php-haken", "unknown") == "certified"
    bridge_open = r1 and not r5
    blockers: List[str] = []
    for rid in MAIN_CLIMB:
        st = statuses.get(rid, "missing")
        if st != "certified":
            blockers.append(f"{rid} is {st} (need certified)")
    if not r5:
        blockers.append("r5-cook-reckhow-bridge is not certified (summit link)")
    summit_ready = r4 and r5
    if summit_ready:
        summary = (
            "Summit packaging is unblocked on ladder status: R4 and R5 are "
            "certified. Remaining work is composing the all systems lower bound "
            "with the Cook Reckhow bridge into a machine checkable P != NP claim."
        )
    else:
        summary = (
            "Toward P vs NP: super polynomial lower bounds for all propositional "
            "proof systems imply NP != coNP (Cook Reckhow), which implies P != NP. "
            "Summit needs R4 class hardness plus a certified R5 bridge."
        )
    print(
        f"[saturday.status] summit r4_certified={r4} r5_certified={r5} "
        f"summit_ready={summit_ready} blockers={len(blockers)}"
    )
    return SummitReadiness(
        r4_certified=r4,
        r5_certified=r5,
        bridge_open=bridge_open,
        summit_ready=summit_ready,
        blockers=blockers,
        summary=summary,
    )


def _choice_dict(choice: ActionChoice) -> Dict[str, str]:
    return {
        "rung": choice.rung,
        "action_type": choice.action_type,
        "target": choice.target,
        "rationale": choice.rationale,
        "workstream": choice.workstream or "",
    }


def _command_for_choice(choice: ActionChoice) -> str:
    return (
        f"satday saturday --rung {choice.rung} --action {choice.action_type}"
    )


def _suggested_commands(
    next_choice: ActionChoice,
    parallel: List[ActionChoice],
) -> List[str]:
    """Concrete CLI commands for the operator."""
    cmds: List[str] = [
        "satday status",
        _command_for_choice(next_choice),
    ]
    if len(parallel) >= 2:
        cmds.append("satday saturday --parallel")
        for choice in parallel:
            cmds.append(_command_for_choice(choice))
        cmds.append("satday loop --parallel --cycles 3 --sleep 90")
    else:
        cmds.append("satday loop --cycles 3 --sleep 90")
    cmds.append("satday loop --parallel")
    seen = set()
    ordered: List[str] = []
    for cmd in cmds:
        if cmd in seen:
            continue
        seen.add(cmd)
        ordered.append(cmd)
    print(f"[saturday.status] suggested_commands={len(ordered)}")
    return ordered


def build_saturday_status(repo_root: Path) -> SaturdayStatus:
    """Assemble status from rung memories and session log."""
    repo_root = Path(repo_root)
    print(f"[saturday.status] build repo_root={repo_root}")
    ctx: CycleContext = load_cycle_context(repo_root)

    rows: List[RungStatusRow] = []
    statuses: Dict[str, str] = {}
    for rung_id in RUNG_IDS:
        if rung_id not in ctx.rungs:
            statuses[rung_id] = "missing"
            rows.append(
                RungStatusRow(
                    rung_id=rung_id,
                    title=RUNG_TITLES.get(rung_id, rung_id),
                    status="missing",
                    memory=f"docs/ladder/rungs/{rung_id}.md",
                )
            )
            continue
        rung = ctx.rungs[rung_id]
        statuses[rung_id] = rung.status
        rows.append(
            RungStatusRow(
                rung_id=rung_id,
                title=RUNG_TITLES.get(rung_id, rung_id),
                status=rung.status,
                memory=str(rung.path.relative_to(repo_root)),
            )
        )

    counts = dict(Counter(r.status for r in rows))
    certified = [r.rung_id for r in rows if r.status == "certified"]
    active_work = [
        r.rung_id
        for r in rows
        if r.status in {"active", "prose_accepted", "blocked"}
    ]

    choice = choose_rung_and_action(ctx)
    parallel = list_parallel_choices(ctx)
    next_cycle = _choice_dict(choice)
    parallel_paths = [_choice_dict(c) for c in parallel]
    suggested = _suggested_commands(choice, parallel)

    recent = _load_recent_sessions(repo_root, limit=5)
    last = recent[-1] if recent else ctx.last_session
    summit = _summit_readiness(statuses)

    return SaturdayStatus(
        rungs=rows,
        counts=counts,
        certified=certified,
        active_work=active_work,
        next_cycle=next_cycle,
        parallel_paths=parallel_paths,
        suggested_commands=suggested,
        summit=summit,
        last_session=last,
        recent_sessions=recent,
        toward_p_vs_np=summit.summary,
    )


def status_to_dict(status: SaturdayStatus) -> Dict[str, Any]:
    """JSON serializable dict."""
    return {
        "rungs": [asdict(r) for r in status.rungs],
        "counts": status.counts,
        "certified": status.certified,
        "active_work": status.active_work,
        "next_cycle": status.next_cycle,
        "parallel_paths": status.parallel_paths,
        "suggested_commands": status.suggested_commands,
        "summit": asdict(status.summit),
        "last_session": status.last_session,
        "recent_sessions": status.recent_sessions,
        "toward_p_vs_np": status.toward_p_vs_np,
    }
