"""
Choose one rung and one action for the local saturday cycle.

Rule based (no LLM): mirrors .cursor/skills/saturday/SKILL.md Step 1.

Parallel workstreams (skill Parallelization):
- R2 owns docs/ladder/rungs/r2-width-machinery.md and non Bridge ProofComplexity Lean
- R5 owns docs/ladder/rungs/r5-cook-reckhow-bridge.md and Bridge Lean
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional

from search.saturday.context import ACTIVE_LIKE, RUNG_IDS, CycleContext

# Disjoint ownership from saturday skill Parallelization table
WORKSTREAM_BY_RUNG = {
    "r2-width-machinery": "R2",
    "r5-cook-reckhow-bridge": "R5",
}


@dataclass
class ActionChoice:
    """Step 1 output payload."""

    rung: str
    action_type: str
    target: str
    rationale: str
    workstream: Optional[str] = None


def workstream_for_rung(rung_id: str) -> Optional[str]:
    """Return parallel workstream id when the rung has exclusive ownership."""
    return WORKSTREAM_BY_RUNG.get(rung_id)


VALID_ACTIONS = frozenset({"prove", "formalize", "falsify", "audit"})


def choose_action_for_rung(
    ctx: CycleContext,
    rung_id: str,
    action_override: Optional[str] = None,
    target_override: Optional[str] = None,
) -> ActionChoice:
    """Pick action for a specific rung (shared by serial and parallel choosers)."""
    if rung_id not in ctx.rungs:
        raise RuntimeError(f"Unknown rung: {rung_id}")
    status = ctx.rungs[rung_id].status
    print(f"[saturday.chooser] action_for_rung rung={rung_id} status={status}")

    if action_override:
        action = action_override
        rationale = f"CLI action override on rung with status {status}"
        target = target_override or _default_target(ctx, rung_id, action)
    else:
        from search.saturday.reflect import suggest_action_override

        forced = suggest_action_override(ctx.repo_root, rung_id)
        if forced in VALID_ACTIONS:
            action = forced
            rationale = f"Reflect/control force_action={forced} (status={status})"
            # Prefer decompose micros when stuck; else import; else default
            target = target_override or _import_or_default_target(
                ctx, rung_id, action
            )
        else:
            decomp_choice = _suggest_decompose(ctx, rung_id)
            if decomp_choice is not None:
                action, target, rationale = decomp_choice
            else:
                import_choice = _suggest_import(ctx, rung_id)
                if import_choice is not None:
                    action, target, rationale = import_choice
                elif status == "prose_accepted":
                    action = "formalize"
                    rationale = "Prose accepted gate passed; formalize is next"
                    target = target_override or _default_target(ctx, rung_id, action)
                elif status == "blocked":
                    action = "prove"
                    rationale = "Rung blocked; change approach with a new prove cycle"
                    target = target_override or _default_target(ctx, rung_id, action)
                elif _needs_falsify(ctx, rung_id):
                    action = "falsify"
                    rationale = "No recent falsify calibration recorded for this rung"
                    target = target_override or _default_target(ctx, rung_id, action)
                elif status == "active":
                    action, rationale = _active_rung_action(ctx, rung_id)
                    target = target_override or _import_or_default_target(
                        ctx, rung_id, action
                    )
                elif status == "proposed":
                    action = "prove"
                    rationale = "Proposed rung needs an adopt decision path via prove content"
                    target = target_override or _default_target(ctx, rung_id, action)
                else:
                    action = "audit"
                    rationale = "Default audit pass for hygiene and barriers"
                    target = target_override or _default_target(ctx, rung_id, action)

    if target_override and action_override:
        target = target_override

    choice = ActionChoice(
        rung=rung_id,
        action_type=action,
        target=target,
        rationale=rationale,
        workstream=workstream_for_rung(rung_id),
    )
    print(f"[saturday.chooser] choice={choice}")
    return choice


def _suggest_decompose(ctx: CycleContext, rung_id: str):
    """Return (action, target, rationale) when a stuck-decompose plan is pending."""
    try:
        from search.saturday.decompose import suggest_decompose_action

        cfg = None
        try:
            from infra.config.loader import load_config

            full = load_config(repo_root=ctx.repo_root)
            cfg = getattr(getattr(full, "saturday_loop", None), "decompose", None)
        except Exception as exc:
            print(f"[saturday.chooser] decompose cfg load skipped: {exc}")
        return suggest_decompose_action(ctx.repo_root, rung_id, cfg)
    except Exception as exc:
        print(f"[saturday.chooser] decompose suggest skipped: {exc}")
        return None


def _suggest_import(ctx: CycleContext, rung_id: str):
    """Return (action, target, rationale) when proof import applies."""
    try:
        from search.saturday.proof_source import suggest_import_action

        return suggest_import_action(ctx.repo_root, rung_id)
    except Exception as exc:
        print(f"[saturday.chooser] import suggest skipped: {exc}")
        return None


def _import_or_default_target(ctx: CycleContext, rung_id: str, action: str) -> str:
    decomp = _suggest_decompose(ctx, rung_id)
    if decomp is not None and decomp[0] == action:
        return decomp[1]
    hint = _suggest_import(ctx, rung_id)
    if hint is not None and hint[0] == action:
        return hint[1]
    return _default_target(ctx, rung_id, action)

def _sessions_for_rung(ctx: CycleContext, rung_id: str) -> List[dict]:
    """Recent session records for one rung, oldest to newest."""
    rows = [s for s in ctx.recent_sessions if s.get("rung") == rung_id]
    print(f"[saturday.chooser] sessions_for_rung={rung_id} count={len(rows)}")
    return rows


def _active_rung_action(ctx: CycleContext, rung_id: str) -> tuple:
    """
    Advance active rungs instead of re-proving forever.

    If the latest local CLI cycle already produced a successful prove (or the
    model asked for formalize), switch to formalize. After repeated formalize
    partials, keep formalizing (draft path) rather than bouncing back to prove.
    """
    history = _sessions_for_rung(ctx, rung_id)
    if not history:
        return "prove", "Active rung needs mathematical content in prose"

    last = history[-1]
    last_action = last.get("action_type")
    last_result = last.get("result")
    raw_next = last.get("next_recommended_action")
    next_action = raw_next if raw_next in VALID_ACTIONS else None
    print(
        f"[saturday.chooser] active history last_action={last_action} "
        f"last_result={last_result} next_action={next_action}"
    )

    if last_action == "prove" and last_result in {"success", "partial"}:
        return (
            "formalize",
            "Prior prove cycle produced prose; formalize is next",
        )
    if last_action == "formalize" and last_result in {"partial", "success"}:
        formalize_partials = [
            s for s in history[-6:]
            if s.get("action_type") == "formalize" and s.get("result") == "partial"
        ]
        if len(formalize_partials) >= 4:
            return (
                "prove",
                "Repeated formalize partials without certification; switch to prove",
            )
        return (
            "formalize",
            "Continue formalize on existing prose and drafts",
        )
    if next_action == "formalize":
        return "formalize", "Last session recommended formalize"
    if last_action == "formalize" and last_result == "blocked":
        return "prove", "Formalize blocked; new prove approach"

    # Avoid thrashing: if last two proves succeeded, force formalize
    recent_proves = [
        s for s in history[-3:]
        if s.get("action_type") == "prove" and s.get("result") == "success"
    ]
    if len(recent_proves) >= 2:
        return (
            "formalize",
            "Multiple successful prove cycles already logged; formalize is next",
        )

    if next_action in VALID_ACTIONS:
        return next_action, f"Follow last session next_recommended_action={next_action}"

    return "prove", "Active rung needs mathematical content in prose"

def _rung_spectral_formalize_blocked(ctx: CycleContext, rung_id: str) -> bool:
    """
    True when this rung's import plan only has spectral Frontier pins left and
    the host Lean module has no analysis surface. Local models must not burn
    wakes inventing Nat witnesses for Gabber Galil.
    """
    try:
        from search.saturday.proof_source import (
            catalog_entries_for_rung,
            load_accepted_plan,
            load_entry_module_text,
            load_proof_import_config,
            module_has_analysis_surface,
            step_needs_analysis_surface,
        )

        cfg = load_proof_import_config(ctx.repo_root)
        entries = catalog_entries_for_rung(cfg, rung_id)
        if not entries:
            return False
        entry = entries[0]
        plan = load_accepted_plan(ctx.repo_root, cfg, entry)
        if plan is None:
            return False
        pending = [
            s
            for s in (plan.get("steps") or [])
            if str(s.get("status", "pending")) != "done"
        ]
        if not pending:
            return False
        if not all(step_needs_analysis_surface(s) for s in pending):
            return False
        module_text = load_entry_module_text(ctx.repo_root, entry)
        blocked = not module_has_analysis_surface(module_text)
        print(
            f"[saturday.chooser] spectral_formalize_blocked rung={rung_id} "
            f"pending={len(pending)} blocked={blocked}"
        )
        return blocked
    except Exception as exc:
        print(f"[saturday.chooser] spectral block check skipped: {exc}")
        return False


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

    Skip rungs whose only remaining import work is spectral Frontier pins
    without an analysis Lean surface (continue on the next actionable rung).
    """
    print(
        f"[saturday.chooser] choose overrides rung={rung_override} "
        f"action={action_override} target={target_override}"
    )

    if rung_override and action_override:
        return choose_action_for_rung(
            ctx, rung_override, action_override, target_override
        )

    ordered = [rid for rid in RUNG_IDS if rid in ctx.rungs]
    candidates = [
        rid
        for rid in ordered
        if ctx.rungs[rid].status in ACTIVE_LIKE
        or ctx.rungs[rid].status == "prose_accepted"
    ]
    preferred = [
        rid
        for rid in candidates
        if ctx.rungs[rid].status in {"active", "prose_accepted"}
    ]
    pool = preferred or candidates
    if not pool:
        pool = [
            rid
            for rid in ordered
            if ctx.rungs[rid].status not in {"certified", "killed"}
        ]
    if not pool:
        raise RuntimeError("No actionable rung found in ladder memories")

    if rung_override:
        rung_id = rung_override
    else:
        runnable = [
            rid for rid in pool if not _rung_spectral_formalize_blocked(ctx, rid)
        ]
        if not runnable:
            print(
                "[saturday.chooser] all preferred rungs spectral-blocked; "
                "falling back to pool[0]"
            )
            runnable = pool
        elif runnable != pool:
            print(
                f"[saturday.chooser] skipped spectral-blocked "
                f"{[r for r in pool if r not in runnable]}; using {runnable[0]}"
            )
        rung_id = runnable[0]
    return choose_action_for_rung(ctx, rung_id, action_override, target_override)


def list_parallel_choices(ctx: CycleContext) -> List[ActionChoice]:
    """
    Disjoint next paths safe to run together (one cycle each).

    Only rungs with an exclusive workstream id are included, at most one per
    workstream. Typical split: R2 formalize plus R5 prove or formalize.
    """
    print("[saturday.chooser] list_parallel_choices")
    ordered = [rid for rid in RUNG_IDS if rid in ctx.rungs]
    actionable = [
        rid
        for rid in ordered
        if ctx.rungs[rid].status in {"active", "prose_accepted", "blocked"}
        and workstream_for_rung(rid) is not None
    ]
    seen_streams = set()
    choices: List[ActionChoice] = []
    for rid in actionable:
        stream = workstream_for_rung(rid)
        if stream in seen_streams:
            continue
        seen_streams.add(stream)
        choices.append(choose_action_for_rung(ctx, rid))
    print(
        f"[saturday.chooser] parallel_paths={len(choices)} "
        f"streams={[c.workstream for c in choices]}"
    )
    return choices


def _needs_falsify(ctx: CycleContext, rung_id: str) -> bool:
    """True when rung memory has no falsify session log mention recently."""
    text = ctx.rungs[rung_id].text.lower()
    if "falsif" in text and "session log" in text.lower():
        session_idx = text.rfind("session log")
        tail = text[session_idx:] if session_idx >= 0 else text
        if "falsif" in tail:
            print(f"[saturday.chooser] falsify already present in {rung_id} log")
            return False
    last = ctx.last_session or {}
    if last.get("rung") == rung_id and last.get("action_type") == "falsify":
        return False
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
