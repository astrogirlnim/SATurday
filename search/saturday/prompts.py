"""
Prompt builders for local saturday roles.

Style invariant from skills: generated prose avoids hyphens as punctuation.
Frontier namespace names come from apply_lean.DEFAULT_FRONTIER_NS (single source).
Open obligations are injected dynamically; no hard-coded pin name lists.
"""

from __future__ import annotations

from search.saturday.apply_lean import DEFAULT_FRONTIER_NS
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
    "No new axioms. Prefer mathlib idioms. Work in progress MUST live in a namespace whose "
    "name contains Frontier and may use sorry. Do not emit import lines. Do not use Lean 3 "
    "begin/end. Use Lean 4 by tactics only. Prefer calling accepted declarations listed in "
    "the prompt; do not re prove theorems that are already accepted. Avoid hyphens as "
    "punctuation in comments; spell connections in words."
)

SYSTEM_AUDIT = (
    "You are the SATurday barrier auditor. Be adversarial. Hunt for relativization, "
    "natural proofs analogues, algebraization, interpolation death, simulation order "
    "mistakes, and statement hygiene failures. Record concrete reasons. Avoid hyphens "
    "as punctuation; spell connections in words."
)


def build_prove_prompt(
    ctx: CycleContext,
    choice: ActionChoice,
    accepted_block: str = "",
) -> str:
    """Prover skill prompt (ordinary or import plan)."""
    rung = ctx.rungs[choice.rung]
    import_block = _import_source_block(ctx, choice)
    accepted_section = ""
    if accepted_block.strip():
        accepted_section = f"""
Known accepted lemmas (smart select; cite when useful; do not re prove):
{accepted_block}
"""
    if import_block:
        task = f"""Task (PROOF IMPORT PLAN):
You are porting a machine checked foreign proof into a Lean plan. Do not write Lean.
1. Restate the Lean Frontier targets with explicit quantifiers.
2. Name a non vacuity witness in our Lean types (mggGraph, HasExpansionInv, etc.).
3. Using ONLY the foreign source excerpts below, develop one ordered import plan:
   numbered steps, each with foreign lemma names, target Lean names, and module.
4. Prefer mapping onto the accepted lemmas listed above when they already exist.
5. Number every gap as routine, hard, or unknown. Critical path close must have
   zero sorry; never propose a Lean axiom that cites the foreign ITP.
6. Self adversarial pass.
7. End with a JSON object after the prose, keys:
   status (success|partial|blocked), notes, next_recommended_action
   (prove|formalize|falsify|audit), gate_pending
   (none|accept_prose|adopt_rung|kill_rung|merge_certified),
   import_plan (object with source_id and steps array; each step has id,
   foreign_lemmas, lean_name, module, status pending|done).

Foreign source excerpts:
{import_block}
"""
    else:
        task = """Task:
1. Restate the target with explicit quantifiers.
2. Name a non vacuity witness.
3. Develop exactly one argument in full prose.
4. Prefer citing accepted lemmas from the smart select list when they apply.
5. Number every gap as routine, hard, or unknown.
6. Self adversarial pass.
7. End with a JSON object on its own after the prose, keys:
   status (success|partial|blocked), notes, next_recommended_action
   (prove|formalize|falsify|audit), gate_pending
   (none|accept_prose|adopt_rung|kill_rung|merge_certified).
"""
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
{accepted_section}
{task}
"""


def build_formalize_prompt(
    ctx: CycleContext,
    choice: ActionChoice,
    module_excerpt: str,
    prior_errors: str = "",
    open_obligations: str = "",
    import_step: dict | None = None,
    frontier_ns: str | None = None,
    accepted_block: str = "",
) -> str:
    """Formalizer skill prompt (ordinary or import cluster / micro-lemma)."""
    rung = ctx.rungs[choice.rung]
    err_block = prior_errors.strip() or "(none yet)"
    obligations = open_obligations.strip() or "(none detected)"
    ns = frontier_ns or DEFAULT_FRONTIER_NS.get(choice.rung, "LocalDraftFrontier")
    import_block = _import_source_block(ctx, choice, import_step=import_step)
    accepted_section = ""
    if accepted_block.strip():
        accepted_section = f"""
{accepted_block}
"""
    import_rules = ""
    if import_block or import_step:
        step = import_step or {}
        lean_name = str(step.get("lean_name") or "")
        lean_sig = str(step.get("lean_sig") or "")
        fill_mode = str(step.get("fill_mode") or "sorry_replace")
        tactics = step.get("allowed_tactics") or ["decide", "omega", "simp", "rfl"]
        unit = str(step.get("unit") or "cluster")
        tactics_s = ", ".join(str(t) for t in tactics)
        micro = ""
        if step and fill_mode == "helper_insert":
            micro = f"""
Micro lemma contract (import ladder unit={unit} fill_mode=helper_insert):
- Emit ONE new Lean helper named exactly: {lean_name}
- Intent: {lean_sig or step.get('goal') or '(port foreign lemma)'}
- Do NOT discharge Frontier sorries in this wake; helpers only.
- No sorry. No axioms. No alternate identifier for the helper name.
- Allowed tactics ONLY: {tactics_s}
- Prefer exact/apply of smart selected accepted decls when they fit.
- Translate the foreign excerpt; keep the surface close to existing Lean names.
"""
        elif step:
            micro = f"""
Micro lemma contract (Qwen sized unit={unit}):
- Discharge exactly this name: {lean_name}
- Signature / intent: {lean_sig or step.get('goal') or '(see Lean excerpt)'}
- Fill mode: {fill_mode} (restate the open sorry decl; replace only the proof)
- Allowed tactics ONLY: {tactics_s}
- Emit the theorem/lemma with `:= by ...` using those tactics; do not invent
  alternate identifiers; do not port whole AFP theories in one wake.
- Optional tiny helpers are allowed only if needed to close that one name.
- Prefer `exact` / `apply` of smart selected accepted decls over new proofs.
"""
        import_rules = f"""
Import cluster rules:
8. Follow the accepted import plan step named in the target.
9. Prefer translating the foreign excerpt below; do not invent alternate
   identifiers that ignore our existing mggGraph surface.
10. Do not add axioms. Do not leave sorry on a declaration you claim to close.
{micro}
Foreign source excerpts for this cluster (truncated for micro steps):
{truncate_for_prompt(import_block, 6000 if step else 14000)}
"""
    helper_only = (
        import_step is not None
        and str((import_step or {}).get("fill_mode") or "") == "helper_insert"
    )
    if helper_only:
        step = import_step or {}
        lean_name = str(step.get("lean_name") or "importHelper")
        task_block = f"""Task:
Emit one Lean 4 fragment that ADDS the new helper `{lean_name}` (import ladder micro).
Requirements:
1. Namespace {ns} only.
2. No imports. No axioms. No sorry.
3. Lean 4 ONLY: `:= by`. NEVER `begin`. NEVER Lean 3 ranges like [0..n].
4. The theorem/lemma name MUST be exactly `{lean_name}` (new decl; not a Frontier pin).
5. Do not restate open Frontier sorry names in this wake.
6. Prefer smart selected accepted declarations above; call them with exact/apply.
7. After the code fence, JSON with status, notes, next_recommended_action=formalize,
   gate_pending.
{import_rules}
"""
    else:
        task_block = f"""Task:
Emit one Lean 4 fragment that DISCHARGES at least one open obligation above.
Requirements:
1. Namespace {ns} only.
2. No imports. No axioms.
3. Lean 4 ONLY: `:= by`. NEVER `begin`. NEVER Lean 3 ranges like [0..n].
4. REQUIRED: restate ONE open obligation name from the list with a real proof
   (not sorry). That name must match exactly so apply can replace the open sorry.
5. Optional: include NEW helper lemmas in the same fragment if they are needed
   to support that discharge. Helpers alone without discharging an open name
   will be rejected.
6. Prefer smart selected accepted declarations above; call them with exact/apply.
   Do not re prove theorems that already appear on that list. Prefer identifiers
   that already appear in the excerpt; do not invent machines or sequencers that
   are not present.
7. After the code fence, JSON with status, notes, next_recommended_action=formalize,
   gate_pending.
{import_rules}
"""
    return f"""Rung id: {choice.rung}
Status: {rung.status}
Target: {choice.target}

Open Frontier sorry obligations (live extract from the Lean home; dynamic):
{obligations}

Rung memory (truncated):
{truncate_for_prompt(rung.text, 6000)}

Existing Lean Frontier excerpt (truncated):
{truncate_for_prompt(module_excerpt, 10000)}
{accepted_section}
Prior lake build or gate errors:
{truncate_for_prompt(err_block, 6000)}

{task_block}
"""


def _import_source_block(
    ctx: CycleContext,
    choice: ActionChoice,
    import_step: dict | None = None,
) -> str:
    """Foreign theory excerpts when the target is an import plan or cluster."""
    from search.saturday.proof_source import (
        build_import_prompt_context,
        catalog_entries_for_rung,
        entry_by_id,
        is_import_target,
        load_proof_import_config,
        parse_import_cluster_target,
        resolve_import_step,
    )

    if not is_import_target(choice.target):
        # Still attach context when chooser used an import rationale
        if "import" not in (choice.rationale or "").lower():
            return ""
    try:
        cfg = load_proof_import_config(ctx.repo_root)
        resolved = resolve_import_step(
            ctx.repo_root, choice.rung, choice.target, cfg
        )
        if resolved:
            entry, _plan, step = resolved
            step = import_step or step
            return build_import_prompt_context(
                ctx.repo_root, cfg, entry, step=step
            )
        entries = catalog_entries_for_rung(cfg, choice.rung)
        if not entries:
            source_id, _ = parse_import_cluster_target(choice.target)
            if source_id:
                entries = [entry_by_id(cfg, source_id)]
        if not entries:
            return ""
        return build_import_prompt_context(
            ctx.repo_root, cfg, entries[0], step=import_step
        )
    except Exception as exc:
        print(f"[saturday.prompts] import block skipped: {exc}")
        return ""


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
