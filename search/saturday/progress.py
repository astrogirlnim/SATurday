"""
Progress snapshot for dashboard and status: rungs, critical pins, control, reflect.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from search.saturday.apply_lean import extract_open_frontier_obligations
from search.saturday.control import load_control
from search.saturday.reflect import CRITICAL_PINS, load_reflect, open_critical_pins
from search.saturday.status import RUNG_TITLES, build_saturday_status, status_to_dict


LEAN_BY_RUNG = {
    "r2-width-machinery": "theory/Theory/ProofComplexity/CSExpansion.lean",
    "r5-cook-reckhow-bridge": "theory/Theory/ProofComplexity/Bridge/ProofSystem.lean",
    "r0-resolution-foundations": "theory/Theory/ProofComplexity/Resolution.lean",
    "r1-php-haken": "theory/Theory/ProofComplexity/PHP.lean",
    "r3-stronger-systems": "theory/Theory/ProofComplexity/Resolution.lean",
    "r4-frontier": "theory/Theory/ProofComplexity/CSExpansion.lean",
}


def _obligations_for_rung(repo_root: Path, rung_id: str) -> List[str]:
    rel = LEAN_BY_RUNG.get(rung_id)
    if not rel:
        return []
    path = repo_root / rel
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8")
    return extract_open_frontier_obligations(text)


def build_progress_snapshot(repo_root: Path) -> Dict[str, Any]:
    """JSON payload for dashboard / API."""
    repo_root = Path(repo_root)
    print(f"[saturday.progress] build snapshot repo={repo_root}")
    status = build_saturday_status(repo_root)
    control = load_control(repo_root)
    reflect = load_reflect(repo_root)

    rung_rows: List[Dict[str, Any]] = []
    critical_total = 0
    critical_open = 0
    for row in status.rungs:
        obs = _obligations_for_rung(repo_root, row.rung_id)
        crit = CRITICAL_PINS.get(row.rung_id, [])
        open_crit = open_critical_pins(obs, row.rung_id)
        critical_total += len(crit)
        critical_open += len(open_crit)
        ref = reflect.rungs.get(row.rung_id)
        closed_crit = [c for c in crit if c not in open_crit]
        pin_pct = (
            int(100 * (len(crit) - len(open_crit)) / len(crit)) if crit else (
                100 if row.status == "certified" else 0
            )
        )
        rung_rows.append(
            {
                "rung_id": row.rung_id,
                "title": row.title,
                "status": row.status,
                "memory": row.memory,
                "open_frontier_sorries": obs,
                "critical_pins": crit,
                "open_critical_pins": open_crit,
                "closed_critical_pins": closed_crit,
                "pin_progress_pct": pin_pct,
                "paused": row.rung_id in control.paused_rungs,
                "force_action": control.force_actions.get(row.rung_id),
                "reflect": {
                    "wakes_without_obligation_progress": (
                        ref.wakes_without_obligation_progress if ref else 0
                    ),
                    "consecutive_near_duplicates": (
                        ref.consecutive_near_duplicates if ref else 0
                    ),
                    "consecutive_same_error": (
                        ref.consecutive_same_error if ref else 0
                    ),
                    "last_action": ref.last_action if ref else "",
                    "last_result": ref.last_result if ref else "",
                }
                if ref
                else None,
            }
        )

    certified = sum(1 for r in status.rungs if r.status == "certified")
    rung_pct = int(100 * certified / max(1, len(status.rungs)))
    pin_pct = (
        int(100 * (critical_total - critical_open) / critical_total)
        if critical_total
        else rung_pct
    )

    sessions_path = repo_root / "search" / "logs" / "saturday_sessions.jsonl"
    recent: List[Dict[str, Any]] = []
    if sessions_path.exists():
        lines = [
            ln for ln in sessions_path.read_text(encoding="utf-8").splitlines() if ln.strip()
        ]
        for ln in lines[-12:]:
            try:
                recent.append(json.loads(ln))
            except json.JSONDecodeError:
                continue

    return {
        "toward_p_vs_np": status.toward_p_vs_np,
        "rung_completion_pct": rung_pct,
        "critical_pin_pct": pin_pct,
        "certified_count": certified,
        "rung_count": len(status.rungs),
        "critical_open": critical_open,
        "critical_total": critical_total,
        "control": control.to_dict(),
        "reflect_updated_at": reflect.updated_at,
        "rungs": rung_rows,
        "next_cycle": status.next_cycle,
        "parallel_paths": status.parallel_paths,
        "suggested_commands": status.suggested_commands
        + [
            "satday dashboard",
            "satday kill --reason 'operator stop'",
            "satday unkill",
        ],
        "recent_sessions": recent,
        "status": status_to_dict(status),
    }
