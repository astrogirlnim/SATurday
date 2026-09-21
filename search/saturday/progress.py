"""
Progress snapshot for dashboard and status: rungs, Frontier obligations, control, reflect.

Pin lists are dynamic extracts of open Frontier sorries (no hard-coded names).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from search.saturday.apply_lean import extract_open_frontier_obligations
from search.saturday.accepted_tree import (
    build_accepted_declaration_tree,
    build_accepted_tree_summary,
)
from search.saturday.control import load_control
from search.saturday.reflect import load_reflect
from search.saturday.status import build_saturday_status, status_to_dict


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
    frontier_open_total = 0
    for row in status.rungs:
        obs = _obligations_for_rung(repo_root, row.rung_id)
        frontier_open_total += len(obs)
        ref = reflect.rungs.get(row.rung_id)
        prev = list(ref.last_obligations) if ref else []
        closed_since = sorted(set(prev) - set(obs)) if prev else []
        # Live pin list = whatever Frontier sorries remain (dynamic).
        pin_pct = 100 if not obs else 0
        if prev and len(prev) > 0:
            closed_n = max(0, len(prev) - len(obs))
            pin_pct = int(100 * closed_n / len(prev))
        rung_rows.append(
            {
                "rung_id": row.rung_id,
                "title": row.title,
                "status": row.status,
                "memory": row.memory,
                "open_frontier_sorries": obs,
                "critical_pins": obs,
                "open_critical_pins": obs,
                "closed_critical_pins": closed_since,
                "pin_progress_pct": pin_pct,
                "paused": row.rung_id in control.paused_rungs,
                "force_action": control.force_actions.get(row.rung_id),
                "force_action_source": control.force_action_sources.get(row.rung_id),
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
    # Aggregate: rungs with zero open Frontier sorries count as clear.
    clear_rungs = sum(1 for r in rung_rows if not r["open_frontier_sorries"])
    pin_pct = int(100 * clear_rungs / max(1, len(rung_rows)))

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

    from search.saturday.live import load_live

    live = load_live(repo_root)

    # Counts only on the hot poll path; full tree is /api/accepted-tree.
    print("[saturday.progress] building accepted_tree summary for progress poll")
    accepted_summary = build_accepted_tree_summary(repo_root)
    print(
        f"[saturday.progress] accepted_tree total="
        f"{accepted_summary.get('total_declarations')}"
    )

    return {
        "toward_p_vs_np": status.toward_p_vs_np,
        "rung_completion_pct": rung_pct,
        "critical_pin_pct": pin_pct,
        "certified_count": certified,
        "rung_count": len(status.rungs),
        "critical_open": frontier_open_total,
        "critical_total": frontier_open_total,
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
        "live": live,
        "status": status_to_dict(status),
        "accepted_tree_summary": accepted_summary,
    }


def build_accepted_tree_snapshot(repo_root: Path) -> Dict[str, Any]:
    """Full accepted-declaration tree with live rung Status lines."""
    repo_root = Path(repo_root)
    print(f"[saturday.progress] build accepted tree snapshot repo={repo_root}")
    # Lightweight Status: reads only (skip full satday status / chooser).
    from search.saturday.context import RUNG_IDS, STATUS_RE

    rung_statuses: Dict[str, str] = {}
    for rung_id in RUNG_IDS:
        path = repo_root / "docs" / "ladder" / "rungs" / f"{rung_id}.md"
        status = "unknown"
        if path.is_file():
            text = path.read_text(encoding="utf-8")
            m = STATUS_RE.search(text)
            if m:
                status = m.group(1)
        rung_statuses[rung_id] = status
        print(f"[saturday.progress] tree status {rung_id}={status}")

    tree = build_accepted_declaration_tree(
        repo_root,
        rung_statuses=rung_statuses,
    )
    print(
        f"[saturday.progress] accepted tree ready "
        f"total={tree['summary']['total_declarations']}"
    )
    return tree
