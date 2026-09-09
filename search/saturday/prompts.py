"""
Prompt builders for local saturday roles.

Style invariant from skills: generated prose avoids hyphens as punctuation.
"""

from __future__ import annotations

from search.saturday.chooser import ActionChoice
from search.saturday.context import CycleContext, truncate_for_prompt


SYSTEM_PROVE = (
    "You are the SATurday prover. Produce prose mathematics only. Never write Lean. "
    "Use complete sentences. Avoid hyphens as punctuation; spell connections in words. "
    "Every attempt ends with a numbered gap list and a self adversarial pass. "
    "Cite external results as known, adaptation, or new."
)

SYSTEM_FORMALIZE = (
    "You are the SATurday formalizer. Emit Lean 4 only inside a fenced lean code block. "
    "No new axioms. Prefer mathlib idioms. Work in progress may use a namespace ending "
    "in Frontier with sorry; accepted code must not. Avoid hyphens as punctuation in "
    "comments; spell connections in words."
)

SYSTEM_AUDIT = (
    "You are the SATurday barrier auditor. Be adversarial. Hunt for relativization, "
    "natural proofs analogues, algebraization, interpolation death, simulation order "
    "mistakes, and statement hygiene failures. Record concrete reasons. Avoid hyphens "
    "as punctuation; spell connections in words."
)


def build_prove_prompt(ctx: CycleContext, choice: ActionChoice) -> str:
    """Prover skill prompt."""
    rung = ctx.rungs[choice.rung]
    return f"""Rung id: {choice.rung}
Status: {rung.status}
Target: {choice.target}
Rationale for this cycle: {choice.rationale}

Sorry inventory (accepted tree):
{ctx.sorry_report}

Disk:
{ctx.disk_report}

Rung memory (truncated):
{truncate_for_prompt(rung.text, 12000)}

Ladder excerpt (truncated):
{truncate_for_prompt(ctx.ladder_text, 4000)}

Task:
1. Restate the target with explicit quantifiers.
2. Name a non vacuity witness.
3. Develop exactly one argument in full prose.
4. Number every gap as routine, hard, or unknown.
5. Self adversarial pass.
6. End with a JSON object on its own after the prose, keys:
   status (success|partial|blocked), notes, next_recommended_action
   (prove|formalize|falsify|audit), gate_pending
   (none|accept_prose|adopt_rung|kill_rung|merge_certified).
"""


def build_formalize_prompt(
    ctx: CycleContext,
    choice: ActionChoice,
    module_excerpt: str,
    prior_errors: str = "",
) -> str:
    """Formalizer skill prompt."""
    rung = ctx.rungs[choice.rung]
    err_block = prior_errors.strip() or "(none yet)"
    return f"""Rung id: {choice.rung}
Status: {rung.status}
Target: {choice.target}

Rung memory (truncated):
{truncate_for_prompt(rung.text, 8000)}

Existing Lean excerpt (truncated):
{truncate_for_prompt(module_excerpt, 10000)}

Prior lake build or gate errors:
{truncate_for_prompt(err_block, 6000)}

Task:
Emit one Lean 4 module fragment that advances the target. Prefer extending an
existing Frontier namespace. Do not invent axioms. After the code fence, emit JSON
with keys status, notes, next_recommended_action, gate_pending.
"""


def build_audit_prompt(ctx: CycleContext, choice: ActionChoice) -> str:
    """Barrier auditor prompt."""
    rung = ctx.rungs[choice.rung]
    return f"""Rung id: {choice.rung}
Status: {rung.status}
Target: {choice.target}

Rung memory (truncated):
{truncate_for_prompt(rung.text, 12000)}

Stop conditions excerpt (truncated):
{truncate_for_prompt(ctx.stop_conditions_text, 3000)}

Checklist excerpt (truncated):
{truncate_for_prompt(ctx.checklist_text, 3000)}

Audit checklist:
1. Relativization
2. Natural proofs analogue
3. Algebraization
4. Interpolation death
5. Simulation order
6. Statement hygiene (quantifiers, non vacuity, falsifiability)

Produce a written audit with a clear verdict, then JSON with keys status
(success|partial|blocked), notes, next_recommended_action, gate_pending.
"""
