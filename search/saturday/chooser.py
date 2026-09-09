"""
Choose one rung and one action for the local saturday cycle.

Rule based (no LLM): mirrors .cursor/skills/saturday/SKILL.md Step 1.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from search.saturday.context import ACTIVE_LIKE, RUNG_IDS, CycleContext


@dataclass
class ActionChoice:
    """Step 1 output payload."""

    rung: str
    action_type: str
    target: str
    rationale: str


def choose_rung_and_action(
    ctx: CycleContext,
    rung_override: Optional[str] = None,
    action_override: Optional[str] = None,
    target_override: Optional[str] = None,
) -> ActionChoice:
    """
    Priority:
    1. lowest active (or prose_accepted) rung
    2. prose_accepted -> formalize
    3. else prove if content needed
    4. else falsify if no recent falsify on this rung
    5. else audit
    """
    print(
        f"[saturday.chooser] choose overrides rung={rung_override} "
        f"action={action_override} target={target_override}"
    )

    if rung_override and action_override:
        target = target_override or _default_target(ctx, rung_override, action_override)
        choice = ActionChoice(
            rung=rung_override,
            action_type=action_override,
            target=target,
            rationale="CLI override of rung and action",
        )
        print(f"[saturday.chooser] override choice={choice}")
        return choice

    ordered = [rid for rid in RUNG_IDS if rid in ctx.rungs]
    candidates = [
        rid
        for rid in ordered
        if ctx.rungs[rid].status in ACTIVE_LIKE
        or ctx.rungs[rid].status == "prose_accepted"
    ]
    # Prefer true active and prose_accepted over blocked when both exist
    preferred = [
        rid
        for rid in candidates
        if ctx.rungs[rid].status in {"active", "prose_accepted"}
    ]
    pool = preferred or candidates
    if not pool:
        # Fall back to lowest non certified proposed rung
        pool = [
            rid
            for rid in ordered
            if ctx.rungs[rid].status not in {"certified", "killed"}
        ]
    if not pool:
        raise RuntimeError("No actionable rung found in ladder memories")

    rung_id = rung_override or pool[0]
    status = ctx.rungs[rung_id].status
    print(f"[saturday.chooser] selected rung={rung_id} status={status}")

    if action_override:
        action = action_override
        rationale = f"CLI action override on rung with status {status}"
    elif status == "prose_accepted":
        action = "formalize"
        rationale = "Prose accepted gate passed; formalize is next"
    elif status == "blocked":
        action = "prove"
        rationale = "Rung blocked; change approach with a new prove cycle"
    elif _needs_falsify(ctx, rung_id):
        action = "falsify"
        rationale = "No recent falsify calibration recorded for this rung"
    elif status == "active":
        action = "prove"
        rationale = "Active rung needs mathematical content in prose"
    else:
        action = "audit"
        rationale = "Default audit pass for hygiene and barriers"

    target = target_override or _default_target(ctx, rung_id, action)
    choice = ActionChoice(
        rung=rung_id,
        action_type=action,
        target=target,
        rationale=rationale,
    )
    print(f"[saturday.chooser] choice={choice}")
    return choice


def _needs_falsify(ctx: CycleContext, rung_id: str) -> bool:
    """True when rung memory has no falsify session log mention recently."""
    text = ctx.rungs[rung_id].text.lower()
    if "falsif" in text and "session log" in text.lower():
        # Heuristic: if falsify appears in session log section, skip
        session_idx = text.rfind("session log")
        tail = text[session_idx:] if session_idx >= 0 else text
        if "falsif" in tail:
            print(f"[saturday.chooser] falsify already present in {rung_id} log")
            return False
    last = ctx.last_session or {}
    if last.get("rung") == rung_id and last.get("action_type") == "falsify":
        return False
    # Only auto falsify on early rungs with empirical families
    if rung_id in {"r1-php-haken", "r2-width-machinery"}:
        print(f"[saturday.chooser] falsify candidate for {rung_id}")
        return "falsif" not in text
    return False


def _default_target(ctx: CycleContext, rung_id: str, action: str) -> str:
    """Pick a short target string from rung statement head."""
    text = ctx.rungs[rung_id].text
    statement = ""
    if "## Statement" in text:
        after = text.split("## Statement", 1)[1]
        statement = after.split("##", 1)[0].strip().splitlines()
        statement = " ".join(ln.strip() for ln in statement[:6] if ln.strip())
    if action == "falsify":
        return f"budgeted calibration for {rung_id}"
    if action == "formalize":
        return f"formalize next Frontier obligation on {rung_id}"
    if action == "audit":
        return f"barrier and hygiene audit of {rung_id}"
    return statement[:240] or f"prove progress on {rung_id}"
