"""
Human readable status lines for satday auto / saturday cycles.

Debug logs stay as [saturday.*]. These lines are for watching the loop.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional


def announce(message: str) -> None:
    """Print one plain status line the operator can skim."""
    print(f">>> {message}", flush=True)


def banner(title: str) -> None:
    """Print a section break."""
    line = "=" * 64
    print(line, flush=True)
    print(f">>> {title}", flush=True)
    print(line, flush=True)


def summarize_record(record: Dict[str, Any]) -> str:
    """One line summary of a finished workstream record."""
    ws = record.get("workstream") or "?"
    rung = record.get("rung") or "?"
    action = record.get("action_type") or "?"
    result = record.get("result") or "?"
    gate = record.get("gate_pending") or "none"
    notes = (record.get("notes") or "").strip().replace("\n", " ")
    if len(notes) > 160:
        notes = notes[:157] + "..."
    return (
        f"[{ws}] {rung} / {action} -> {result} "
        f"(gate={gate}). {notes}"
    )


def summarize_wave(wake: int, records: List[Dict[str, Any]]) -> None:
    """Print a readable wake summary."""
    banner(f"Wake {wake} complete")
    if not records:
        announce("No workstreams ran.")
        return
    results = [r.get("result") for r in records]
    if all(r == "success" for r in results):
        announce("All workstreams succeeded this wake.")
    elif all(r == "partial" for r in results):
        announce(
            "Partial progress only. Auto will retry with compile errors "
            "fed back into the next formalize prompt."
        )
    elif any(r == "blocked" for r in results):
        announce("At least one workstream is blocked; check notes below.")
    else:
        announce(f"Mixed results: {results}")
    for record in records:
        announce(summarize_record(record))


def explain_apply_outcome(
    *,
    applied: bool,
    reverted: bool,
    build_ok: bool,
    notes: str,
    build_tail: str = "",
) -> None:
    """Human explanation after auto-apply."""
    if applied and build_ok:
        announce(f"Lean accepted and kept in theory/: {notes}")
        return
    if reverted:
        announce("Lean draft did not compile. Reverted theory/ to the last green tree.")
        digest = (build_tail or notes).strip().replace("\n", " | ")
        if len(digest) > 240:
            digest = digest[:237] + "..."
        announce(f"Compile digest for next wake: {digest}")
        announce("Next formalize wake will see this error and try a corrected draft.")
        return
    announce(f"Draft not applied: {notes}")
