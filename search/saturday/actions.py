"""
Run one saturday action: prove, formalize, falsify, or audit.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

from infra.config.schemas import SaturdayLoopConfig, SaturdayRoleLLMConfig
from search.llm.client import LLMRequest, LocalLLMClient
from search.saturday.chooser import ActionChoice
from search.saturday.context import CycleContext, truncate_for_prompt
from search.saturday import prompts as prompt_builders
from search.saturday.ui import announce, explain_apply_outcome


LEAN_FENCE_RE = re.compile(r"```lean\s*(.*?)```", re.DOTALL | re.IGNORECASE)
JSON_RE = re.compile(r"\{[^{}]*\"status\"[^{}]*\}", re.DOTALL)


@dataclass
class ActionResult:
    """Role skill return payload plus gate hint."""

    status: str
    artifact_refs: List[str] = field(default_factory=list)
    notes: str = ""
    next_recommended_action: str = "prove"
    gate_pending: str = "none"
    memory_entry: str = ""
    raw_model_text: str = ""


def run_action(
    ctx: CycleContext,
    choice: ActionChoice,
    loop_cfg: SaturdayLoopConfig,
    client: Optional[LocalLLMClient],
) -> ActionResult:
    """Dispatch one action."""
    print(
        f"[saturday.actions] run_action type={choice.action_type} "
        f"rung={choice.rung} target={choice.target!r}"
    )
    if choice.action_type == "prove":
        assert client is not None
        return _run_prove(ctx, choice, loop_cfg.prove, client, loop_cfg)
    if choice.action_type == "formalize":
        assert client is not None
        return _run_formalize(ctx, choice, loop_cfg, client)
    if choice.action_type == "falsify":
        return _run_falsify(ctx, choice, loop_cfg)
    if choice.action_type == "audit":
        assert client is not None
        return _run_audit(ctx, choice, loop_cfg.audit, client, loop_cfg)
    raise ValueError(f"Unknown action_type: {choice.action_type}")


def _role_request(
    loop_cfg: SaturdayLoopConfig,
    role: SaturdayRoleLLMConfig,
    prompt: str,
    system: str,
    *,
    model_override: Optional[str] = None,
    api_style_override: Optional[str] = None,
) -> LLMRequest:
    return LLMRequest(
        model=model_override or role.model,
        prompt=prompt,
        system=system,
        temperature=role.temperature,
        num_predict=role.num_predict,
        api_style=api_style_override or loop_cfg.api_style,
    )


def _parse_trailing_json(text: str) -> Dict[str, Any]:
    """Best effort extract of the status JSON object from model output."""
    print(f"[saturday.actions] parse JSON from model text chars={len(text)}")
    candidates = list(JSON_RE.finditer(text))
    if not candidates:
        # Try last brace block
        start = text.rfind("{")
        end = text.rfind("}")
        if start >= 0 and end > start:
            blob = text[start : end + 1]
            try:
                data = json.loads(blob)
                print(f"[saturday.actions] parsed JSON keys={list(data)}")
                return data
            except json.JSONDecodeError:
                pass
        print("[saturday.actions] no JSON found; defaulting status=partial")
        return {
            "status": "partial",
            "notes": "Model omitted machine JSON; see prose in notes",
            "next_recommended_action": "prove",
            "gate_pending": "none",
        }
    blob = candidates[-1].group(0)
    try:
        data = json.loads(blob)
        print(f"[saturday.actions] parsed JSON keys={list(data)}")
        return data
    except json.JSONDecodeError as exc:
        print(f"[saturday.actions] JSON parse failed: {exc}")
        return {
            "status": "partial",
            "notes": f"JSON parse failed: {exc}",
            "next_recommended_action": "prove",
            "gate_pending": "none",
        }


def _dated_entry(action: str, result: str, artifacts: List[str], learned: str) -> str:
    day = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    arts = ", ".join(artifacts) if artifacts else "(none)"
    return (
        f"- {day} local saturday {action}: result={result}; "
        f"artifacts: {arts}; learned: {learned.strip()}"
    )


def _run_prove(
    ctx: CycleContext,
    choice: ActionChoice,
    role: SaturdayRoleLLMConfig,
    client: LocalLLMClient,
    loop_cfg: SaturdayLoopConfig,
) -> ActionResult:
    from search.saturday.llm_factory import (
        make_remote_client,
        remote_config,
        remote_model_for,
        want_remote_prove,
    )

    from search.saturday.accepted_select import select_from_loop_config

    prove_sel = select_from_loop_config(
        ctx.repo_root,
        loop_cfg,
        rung_id=choice.rung,
        target=choice.target,
        open_obligations=[],
        module_excerpt="",
        prior_errors="",
        extra_text=ctx.rungs[choice.rung].text[:2000],
    )
    accepted_block = prove_sel.format_block(max_chars=2500)
    print(
        f"[saturday.actions] prove accepted_select n={len(prove_sel.names)} "
        f"of {prove_sel.pool_size}"
    )
    prompt = prompt_builders.build_prove_prompt(
        ctx, choice, accepted_block=accepted_block
    )
    gen_client = client
    model = role.model
    api_style = loop_cfg.api_style
    tag = "local"
    if want_remote_prove(loop_cfg):
        remote = remote_config(loop_cfg)
        gen_client = make_remote_client(loop_cfg)
        model = remote_model_for(loop_cfg, "prove")
        api_style = remote.api_style
        tag = "openrouter"
        announce(f"Prove via OpenRouter model {model} (theorizing).")
    print(f"[saturday.actions] prove tag={tag} model={model}")
    try:
        resp = gen_client.generate(
            _role_request(
                loop_cfg,
                role,
                prompt,
                prompt_builders.SYSTEM_PROVE,
                model_override=model,
                api_style_override=api_style,
            )
        )
    except Exception as exc:
        remote = remote_config(loop_cfg)
        fallback = getattr(remote, "prove_fallback_model", "") or ""
        if want_remote_prove(loop_cfg) and fallback and fallback != model:
            announce(f"Prove primary model failed ({exc}); trying fallback {fallback}")
            resp = gen_client.generate(
                _role_request(
                    loop_cfg,
                    role,
                    prompt,
                    prompt_builders.SYSTEM_PROVE,
                    model_override=fallback,
                    api_style_override=api_style,
                )
            )
        else:
            raise
    meta = _parse_trailing_json(resp.text)
    status = str(meta.get("status", "partial"))
    notes = str(meta.get("notes") or resp.text[-1200:])
    next_action = str(meta.get("next_recommended_action", "audit"))
    if next_action not in {"prove", "formalize", "falsify", "audit"}:
        print(
            f"[saturday.actions] sanitize next_recommended_action "
            f"from {next_action!r} to formalize"
        )
        next_action = "formalize"
    gate = str(meta.get("gate_pending", "accept_prose" if status == "success" else "none"))
    if gate == "adopt_rung" and ctx.rungs[choice.rung].status == "active":
        gate = "accept_prose" if status == "success" else "none"
        print(f"[saturday.actions] sanitize gate_pending adopt_rung -> {gate}")
    artifact = str(ctx.rungs[choice.rung].path.relative_to(ctx.repo_root))
    prose_path = _write_draft(
        ctx.repo_root,
        loop_cfg.draft_dir,
        f"{choice.rung}_prove_{tag}.md",
        resp.text,
    )
    plan_refs: List[str] = []
    plan_meta = meta.get("import_plan")
    if isinstance(plan_meta, dict) and plan_meta.get("steps"):
        try:
            from search.saturday.proof_source import (
                catalog_entries_for_rung,
                entry_by_id,
                is_import_target,
                load_proof_import_config,
                save_accepted_plan,
            )

            if is_import_target(choice.target) or status == "success":
                cfg = load_proof_import_config(ctx.repo_root)
                entries = catalog_entries_for_rung(cfg, choice.rung)
                if not entries and is_import_target(choice.target):
                    tid = choice.target.split(":", 1)[1].strip().split()[0]
                    entries = [entry_by_id(cfg, tid)]
                if entries and (
                    status == "success" or gate == "accept_prose"
                ):
                    # Persist plan draft; gate_auto accept will treat as accepted
                    path = save_accepted_plan(
                        ctx.repo_root, cfg, entries[0], plan_meta
                    )
                    plan_refs.append(str(path.relative_to(ctx.repo_root)))
                    print(
                        f"[saturday.actions] import plan saved path={path} "
                        f"steps={len(plan_meta.get('steps') or [])}"
                    )
                    notes = (notes + f" | import_plan_saved={path.name}")[:2000]
                    if next_action == "audit":
                        next_action = "formalize"
        except Exception as exc:
            print(f"[saturday.actions] import plan save skipped: {exc}")
    memory = _dated_entry(
        "prove",
        status,
        [artifact, str(prose_path.relative_to(ctx.repo_root))] + plan_refs,
        notes[:500],
    )
    memory = memory + "\n\n" + truncate_for_prompt(resp.text, 8000)
    return ActionResult(
        status=status,
        artifact_refs=[artifact, str(prose_path.relative_to(ctx.repo_root))]
        + plan_refs,
        notes=notes[:2000],
        next_recommended_action=next_action,
        gate_pending=gate,
        memory_entry=memory,
        raw_model_text=resp.text,
    )


def _run_audit(
    ctx: CycleContext,
    choice: ActionChoice,
    role: SaturdayRoleLLMConfig,
    client: LocalLLMClient,
    loop_cfg: SaturdayLoopConfig,
) -> ActionResult:
    prompt = prompt_builders.build_audit_prompt(ctx, choice)
    print(f"[saturday.actions] audit model={role.model}")
    resp = client.generate(_role_request(loop_cfg, role, prompt, prompt_builders.SYSTEM_AUDIT))
    meta = _parse_trailing_json(resp.text)
    status = str(meta.get("status", "partial"))
    notes = str(meta.get("notes") or resp.text[-1200:])
    next_action = str(meta.get("next_recommended_action", "prove"))
    gate = str(meta.get("gate_pending", "none"))
    artifact = str(ctx.rungs[choice.rung].path.relative_to(ctx.repo_root))
    draft = _write_draft(
        ctx.repo_root,
        loop_cfg.draft_dir,
        f"{choice.rung}_audit.md",
        resp.text,
    )
    memory = _dated_entry(
        "audit",
        status,
        [artifact, str(draft.relative_to(ctx.repo_root))],
        notes[:500],
    )
    memory = memory + "\n\n" + truncate_for_prompt(resp.text, 6000)
    return ActionResult(
        status=status,
        artifact_refs=[artifact, str(draft.relative_to(ctx.repo_root))],
        notes=notes[:2000],
        next_recommended_action=next_action,
        gate_pending=gate,
        memory_entry=memory,
        raw_model_text=resp.text,
    )


def _guess_lean_target(ctx: CycleContext, choice: ActionChoice) -> Path:
    """Map rung id to a primary Lean file under theory/.

    Import plan steps may pin a different module (e.g. MGG.lean for R2 Block A).
    """
    try:
        from search.saturday.proof_source import (
            load_proof_import_config,
            resolve_import_step,
        )

        pi_cfg = load_proof_import_config(ctx.repo_root)
        resolved = resolve_import_step(
            ctx.repo_root, choice.rung, choice.target, pi_cfg
        )
        if resolved:
            _entry, _plan, step = resolved
            mod = str(step.get("module") or "").strip()
            if mod:
                path = ctx.repo_root / mod
                print(
                    f"[saturday.actions] lean target from import step "
                    f"module={mod} exists={path.exists()}"
                )
                if path.exists():
                    return path
    except Exception as exc:
        print(f"[saturday.actions] import lean target resolve skipped: {exc}")

    blob = f"{choice.target} {choice.rationale}".lower()
    if choice.rung == "r2-width-machinery" and (
        "mgg" in blob or "gabber" in blob or "cheeger" in blob
    ):
        mgg = ctx.repo_root / "theory/Theory/ProofComplexity/MGG.lean"
        if mgg.exists():
            print(f"[saturday.actions] lean target MGG hint path={mgg}")
            return mgg

    mapping = {
        "r0-resolution-foundations": "theory/Theory/ProofComplexity/Resolution.lean",
        "r1-php-haken": "theory/Theory/ProofComplexity/PHP.lean",
        # Default R2 home is CSExpansionFrontier; MGG override above when hinted
        "r2-width-machinery": "theory/Theory/ProofComplexity/CSExpansion.lean",
        "r3-stronger-systems": "theory/Theory/ProofComplexity/Resolution.lean",
        "r4-frontier": "theory/Theory/ProofComplexity/CSExpansion.lean",
        "r5-cook-reckhow-bridge": "theory/Theory/ProofComplexity/Bridge/ProofSystem.lean",
    }
    rel = mapping.get(choice.rung, "theory/Theory/ProofComplexity/Resolution.lean")
    path = ctx.repo_root / rel
    print(f"[saturday.actions] lean target guess={path}")
    return path


def _run_formalize(
    ctx: CycleContext,
    choice: ActionChoice,
    loop_cfg: SaturdayLoopConfig,
    client: LocalLLMClient,
) -> ActionResult:
    from search.saturday.apply_lean import apply_frontier_draft, lake_build_locked
    from search.saturday.accepted_select import select_from_loop_config
    from search.saturday.llm_factory import (
        make_remote_client,
        remote_config,
        want_remote_formalize,
    )

    role = loop_cfg.formalize
    lean_path = _guess_lean_target(ctx, choice)
    import_step: Optional[dict] = None
    frontier_ns: Optional[str] = None
    try:
        from search.saturday.proof_source import (
            frontier_ns_for_module,
            load_proof_import_config,
            resolve_import_step,
        )

        pi_cfg = load_proof_import_config(ctx.repo_root)
        resolved = resolve_import_step(
            ctx.repo_root, choice.rung, choice.target, pi_cfg
        )
        if resolved:
            _entry, _plan, import_step = resolved
            mod = str((import_step or {}).get("module") or "")
            if mod:
                frontier_ns = frontier_ns_for_module(mod)
            print(
                f"[saturday.actions] formalize import_step="
                f"{(import_step or {}).get('id')} frontier_ns={frontier_ns}"
            )
    except Exception as exc:
        print(f"[saturday.actions] import_step resolve skipped: {exc}")

    if frontier_ns is None:
        try:
            from search.saturday.proof_source import frontier_ns_for_module

            frontier_ns = frontier_ns_for_module(
                str(lean_path.relative_to(ctx.repo_root))
            )
        except Exception:
            frontier_ns = None

    module_excerpt = ""
    open_obs = ""
    open_names: List[str] = []
    if lean_path.exists():
        from search.saturday.apply_lean import extract_open_frontier_obligations

        full = lean_path.read_text(encoding="utf-8")
        module_excerpt = _frontier_focus_excerpt(full)
        open_names = extract_open_frontier_obligations(module_excerpt)
        if not open_names:
            open_names = extract_open_frontier_obligations(full)
        open_obs = "\n".join(f"- {n}" for n in open_names) if open_names else ""
        print(f"[saturday.actions] open Frontier obligations={open_names}")
        if open_names:
            announce(
                f"Open Frontier obligations for {choice.rung}: "
                + ", ".join(open_names)
            )
        else:
            announce(
                f"No open Frontier sorry found in {lean_path.name}; "
                "model will still try a helper lemma."
            )
    else:
        module_excerpt = f"(missing file {lean_path})"

    build = lake_build_locked(ctx.repo_root)
    prior_errors = ""
    if not build["ok"]:
        from search.saturday.apply_lean import build_error_digest

        prior_errors = build_error_digest(build["output"], limit=6000)
    last_apply_err = _latest_apply_error(
        ctx.repo_root, loop_cfg.draft_dir, choice.rung
    )
    if last_apply_err:
        prior_errors = (
            (prior_errors + "\n\n" if prior_errors else "")
            + "Last auto-apply lake failure:\n"
            + last_apply_err
        )
    print(f"[saturday.actions] formalize ambient_build_ok={build['ok']}")

    extra = ""
    if import_step:
        extra = " ".join(
            str(x)
            for x in [
                import_step.get("lean_name"),
                import_step.get("goal"),
                " ".join(
                    str(t) for t in (import_step.get("foreign_lemmas") or [])
                ),
            ]
            if x
        )
    sel = select_from_loop_config(
        ctx.repo_root,
        loop_cfg,
        rung_id=choice.rung,
        target=choice.target,
        open_obligations=open_names,
        module_excerpt=module_excerpt,
        prior_errors=prior_errors,
        extra_text=extra,
    )
    accepted_block = sel.format_block(max_chars=4000)
    announce(
        f"Accepted smart select: {len(sel.names)} of {sel.pool_size} decls "
        f"for {choice.rung}"
    )

    remote = remote_config(loop_cfg)
    use_remote = want_remote_formalize(loop_cfg)
    remote_only = use_remote and remote.mode == "remote"

    def one_pass(
        *,
        gen_client: LocalLLMClient,
        model: str,
        api_style: str,
        tag: str,
        err_ctx: str,
    ) -> dict:
        announce(
            f"Asking {tag} model {model} for a Lean 4 Frontier draft "
            f"(error context: {len(err_ctx)} chars)."
        )
        prompt = prompt_builders.build_formalize_prompt(
            ctx,
            choice,
            module_excerpt,
            prior_errors=err_ctx,
            open_obligations=open_obs,
            import_step=import_step,
            frontier_ns=frontier_ns,
            accepted_block=accepted_block,
        )
        print(
            f"[saturday.actions] formalize prompt_chars={len(prompt)} "
            f"accepted_block_chars={len(accepted_block)} "
            f"frontier_ns={frontier_ns}"
        )
        resp = gen_client.generate(
            _role_request(
                loop_cfg,
                role,
                prompt,
                prompt_builders.SYSTEM_FORMALIZE,
                model_override=model,
                api_style_override=api_style,
            )
        )
        fence = LEAN_FENCE_RE.search(resp.text)
        lean_code = fence.group(1).strip() if fence else resp.text
        draft_path = _write_draft(
            ctx.repo_root,
            loop_cfg.draft_dir,
            f"{choice.rung}_formalize_{tag}.lean",
            lean_code + "\n",
        )
        meta = _parse_trailing_json(resp.text)
        arts = [
            str(draft_path.relative_to(ctx.repo_root)),
            str(lean_path.relative_to(ctx.repo_root)) if lean_path.exists() else "",
        ]
        arts = [a for a in arts if a]
        notes = str(
            meta.get("notes")
            or f"Lean draft ({tag}) at {draft_path.relative_to(ctx.repo_root)}"
        )
        notes = f"{notes} | accepted_select={len(sel.names)}/{sel.pool_size}"
        apply_notes = "auto_apply disabled"
        status = "partial"
        gate = "none"
        applied_ok = False
        build_tail = ""
        if getattr(loop_cfg, "auto_apply", True):
            announce(
                f"Auto-apply ({tag}): merge into {lean_path.name}, lake build, "
                "revert if red."
            )
            applied = apply_frontier_draft(
                repo_root=ctx.repo_root,
                lean_path=lean_path,
                lean_code=lean_code,
                rung_id=choice.rung,
            )
            apply_notes = applied.notes
            build_tail = applied.build_tail or ""
            explain_apply_outcome(
                applied=applied.applied,
                reverted=applied.reverted,
                build_ok=applied.build_ok,
                notes=applied.notes,
                build_tail=applied.build_tail,
            )
            if applied.build_tail:
                err_draft = _write_draft(
                    ctx.repo_root,
                    loop_cfg.draft_dir,
                    f"{choice.rung}_apply_error.txt",
                    applied.build_tail,
                )
                arts.append(str(err_draft.relative_to(ctx.repo_root)))
            if applied.applied and applied.build_ok:
                applied_ok = True
                # sorry-free helper is progress, not rung certification
                from search.saturday.apply_lean import extract_open_frontier_obligations

                remaining = []
                if lean_path.exists():
                    remaining = extract_open_frontier_obligations(
                        lean_path.read_text(encoding="utf-8")
                    )
                if remaining:
                    status = "partial"
                    gate = "none"
                    announce(
                        f"Apply stuck in theory/, but Frontier sorries remain: "
                        + ", ".join(remaining[:6])
                    )
                elif applied.has_sorry:
                    status = "partial"
                    gate = "none"
                else:
                    status = "success"
                    gate = "merge_certified"
                arts.append(applied.target)
            else:
                status = "partial"
        else:
            notes = notes + " Local CLI writes drafts only; auto_apply is false."
        return {
            "status": status,
            "gate": gate,
            "notes": f"{notes} {apply_notes}",
            "arts": arts,
            "lean_code": lean_code,
            "raw": resp.text,
            "applied_ok": applied_ok,
            "build_tail": build_tail,
            "tag": tag,
            "model": model,
        }

    if remote_only:
        from search.saturday.llm_factory import remote_model_for

        rclient = make_remote_client(loop_cfg)
        primary = remote_model_for(loop_cfg, "formalize")
        announce(f"Formalize via OpenRouter model {primary} (Lean prover oriented).")
        try:
            outcome = one_pass(
                gen_client=rclient,
                model=primary,
                api_style=remote.api_style,
                tag="openrouter",
                err_ctx=prior_errors,
            )
        except Exception as exc:
            fallback = getattr(remote, "formalize_fallback_model", "") or ""
            if fallback and fallback != primary:
                announce(
                    f"Formalize primary model failed ({exc}); "
                    f"trying fallback {fallback}"
                )
                outcome = one_pass(
                    gen_client=rclient,
                    model=fallback,
                    api_style=remote.api_style,
                    tag="openrouter_fallback",
                    err_ctx=prior_errors,
                )
            else:
                raise
    else:
        outcome = one_pass(
            gen_client=client,
            model=role.model,
            api_style=loop_cfg.api_style,
            tag="local",
            err_ctx=prior_errors,
        )
        if (
            use_remote
            and remote.mode == "escalate"
            and not outcome["applied_ok"]
            and getattr(loop_cfg, "auto_apply", True)
        ):
            announce(
                "Local formalize did not stick. Escalating once to OpenRouter "
                f"({remote.formalize_model})."
            )
            pieces = []
            if prior_errors.strip():
                pieces.append("Prior lake or apply errors:\n" + prior_errors.strip())
            if outcome.get("build_tail"):
                pieces.append(
                    "Local attempt compile digest:\n" + outcome["build_tail"].strip()
                )
            local_notes = (outcome.get("notes") or "").strip()
            if local_notes:
                pieces.append("Local attempt outcome (reject or revert):\n" + local_notes[:2000])
            local_lean = (outcome.get("lean_code") or "").strip()
            if local_lean:
                pieces.append(
                    "Local draft that failed (do not repeat its mistakes):\n"
                    + local_lean[:3000]
                )
            pieces.append(
                "Target only open Frontier obligations for this rung. "
                "For R2 prefer exists_spreads_matchable_unsat_random3CNF or "
                "exists_cs_clause_expanding_3cnf helpers; never reinvent width graft."
            )
            escalated_err = "\n\n".join(pieces)
            announce(
                f"OpenRouter escalate context chars={len(escalated_err)} "
                f"(includes local reject/compile notes)."
            )
            try:
                rclient = make_remote_client(loop_cfg)
                remote_out = one_pass(
                    gen_client=rclient,
                    model=remote.formalize_model,
                    api_style=remote.api_style,
                    tag="openrouter",
                    err_ctx=escalated_err,
                )
                # Prefer remote outcome; keep local draft refs
                remote_out["arts"] = list(
                    dict.fromkeys(outcome["arts"] + remote_out["arts"])
                )
                remote_out["notes"] = (
                    f"local:{outcome['notes'][:400]} | remote:{remote_out['notes']}"
                )
                outcome = remote_out
            except Exception as exc:
                announce(f"OpenRouter escalation failed: {exc}")
                outcome["notes"] = outcome["notes"] + f" OpenRouter escalate failed: {exc}"

    next_action = "formalize"
    notes = outcome["notes"]
    if not build["ok"]:
        notes = notes + f" Ambient lake build was red (tail): {prior_errors[-800:]}"

    memory = _dated_entry("formalize", outcome["status"], outcome["arts"], notes[:500])
    memory = memory + "\n\n" + truncate_for_prompt(outcome["lean_code"], 4000)
    return ActionResult(
        status=outcome["status"],
        artifact_refs=outcome["arts"],
        notes=notes[:2000],
        next_recommended_action=next_action,
        gate_pending=outcome["gate"],
        memory_entry=memory,
        raw_model_text=outcome["raw"],
    )


def _run_falsify(
    ctx: CycleContext,
    choice: ActionChoice,
    loop_cfg: SaturdayLoopConfig,
) -> ActionResult:
    """No LLM: budgeted baseline runner."""
    script = ctx.repo_root / "search" / "bin" / "run_proof_size_baseline.py"
    cmd = [
        "python3",
        str(script),
        "--family",
        loop_cfg.falsify_family,
        "--n-min",
        str(loop_cfg.falsify_n_min),
        "--n-max",
        str(loop_cfg.falsify_n_max),
        "--seed",
        str(loop_cfg.falsify_seed),
    ]
    print(f"[saturday.actions] falsify cmd={' '.join(cmd)}")
    proc = subprocess.run(
        cmd,
        cwd=str(ctx.repo_root),
        capture_output=True,
        text=True,
        check=False,
    )
    combined = (proc.stdout or "") + "\n" + (proc.stderr or "")
    print(f"[saturday.actions] falsify exit={proc.returncode} out_chars={len(combined)}")
    log_path = "search/logs/falsifier_runs.jsonl"
    status = "success" if proc.returncode == 0 else "blocked"
    notes = (
        f"Falsify family={loop_cfg.falsify_family} "
        f"n={loop_cfg.falsify_n_min}..{loop_cfg.falsify_n_max} "
        f"seed={loop_cfg.falsify_seed} exit={proc.returncode}. "
        f"Tail: {combined[-1200:]}"
    )
    arts = [log_path]
    memory = _dated_entry("falsify", status, arts, notes[:500])
    return ActionResult(
        status=status,
        artifact_refs=arts,
        notes=notes[:2000],
        next_recommended_action="prove" if status == "success" else "falsify",
        gate_pending="none",
        memory_entry=memory,
        raw_model_text=combined[-4000:],
    )


def _run_lake_build(repo_root: Path) -> Dict[str, Any]:
    """Run lake build in theory/; return ok flag and output."""
    theory = repo_root / "theory"
    print(f"[saturday.actions] lake build in {theory}")
    proc = subprocess.run(
        ["lake", "build"],
        cwd=str(theory),
        capture_output=True,
        text=True,
        check=False,
    )
    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    ok = proc.returncode == 0
    print(f"[saturday.actions] lake build ok={ok} exit={proc.returncode}")
    return {"ok": ok, "output": output, "returncode": proc.returncode}


def _frontier_focus_excerpt(source: str, max_chars: int = 12000) -> str:
    """Prefer the last *Frontier namespace block (open sorries) over file tail."""
    matches = list(re.finditer(r"(?m)^namespace \S*Frontier\b", source))
    if matches:
        start = matches[-1].start()
        chunk = source[start:]
        print(
            f"[saturday.actions] frontier excerpt from idx={start} "
            f"chars={min(len(chunk), max_chars)}"
        )
        if len(chunk) > max_chars:
            return chunk[:max_chars]
        return chunk
    print("[saturday.actions] no Frontier namespace; using file tail")
    return source[-max_chars:]


def _latest_apply_error(repo_root: Path, draft_dir: str, rung_id: str) -> str:
    """Load the newest auto-apply lake error artifact for this rung, if any."""
    directory = repo_root / draft_dir
    if not directory.is_dir():
        return ""
    pattern = f"*_{rung_id}_apply_error.txt"
    files = sorted(directory.glob(pattern), key=lambda p: p.name, reverse=True)
    if not files:
        return ""
    text = files[0].read_text(encoding="utf-8")
    print(f"[saturday.actions] loaded prior apply error path={files[0].name}")
    return text[-6000:]


def _write_draft(repo_root: Path, draft_dir: str, name: str, content: str) -> Path:
    """Write a draft artifact under search/logs/saturday_drafts."""
    directory = repo_root / draft_dir
    directory.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    path = directory / f"{stamp}_{name}"
    path.write_text(content, encoding="utf-8")
    print(f"[saturday.actions] draft written path={path} bytes={len(content)}")
    return path
