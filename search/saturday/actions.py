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
    response_format: Optional[str] = None,
) -> LLMRequest:
    return LLMRequest(
        model=model_override or role.model,
        prompt=prompt,
        system=system,
        temperature=role.temperature,
        num_predict=role.num_predict,
        api_style=api_style_override or loop_cfg.api_style,
        response_format=response_format,
    )


def _parse_trailing_json(text: str) -> Dict[str, Any]:
    """Best effort extract of the status JSON object from model output."""
    print(f"[saturday.actions] parse JSON from model text chars={len(text)}")
    # Prefer first full object when response_format=json_object (whole body).
    stripped = (text or "").strip()
    if stripped.startswith("{"):
        try:
            data, _end = json.JSONDecoder().raw_decode(stripped)
            if isinstance(data, dict) and (
                "status" in data
                or "decl_name" in data
                or "uses" in data
                or "lean" in data
            ):
                print(f"[saturday.actions] parsed JSON keys={list(data)}")
                return data
        except json.JSONDecodeError:
            pass
    # Prefer last object that json-decodes (supports uses: [...] arrays).
    start = text.rfind("{")
    while start >= 0:
        try:
            data, _end = json.JSONDecoder().raw_decode(text[start:])
            if isinstance(data, dict) and (
                "status" in data
                or "decl_name" in data
                or "uses" in data
                or "lean" in data
            ):
                print(f"[saturday.actions] parsed JSON keys={list(data)}")
                return data
        except json.JSONDecodeError:
            pass
        start = text.rfind("{", 0, start)
    candidates = list(JSON_RE.finditer(text))
    if candidates:
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
    print("[saturday.actions] no JSON found; defaulting status=partial")
    return {
        "status": "partial",
        "notes": "Model omitted machine JSON; see prose in notes",
        "next_recommended_action": "prove",
        "gate_pending": "none",
    }


def _lean_from_formalize_response(resp_text: str, meta: Dict[str, Any]) -> str:
    """
    Prefer structured envelope field `lean`; else fenced lean block; else raw.
    """
    lean = meta.get("lean")
    if isinstance(lean, str) and lean.strip():
        print(
            f"[saturday.actions] lean from structured JSON chars={len(lean.strip())}"
        )
        return lean.strip()
    fence = LEAN_FENCE_RE.search(resp_text or "")
    if fence:
        body = fence.group(1).strip()
        print(f"[saturday.actions] lean from fence chars={len(body)}")
        return body
    print("[saturday.actions] lean fallback to raw model text")
    return (resp_text or "").strip()


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
        from search.saturday.decompose import (
            is_decompose_target,
            resolve_decompose_step,
        )
        from infra.config.schemas import SaturdayDecomposeConfig

        if is_decompose_target(choice.target):
            dcfg = getattr(loop_cfg, "decompose", None) or SaturdayDecomposeConfig()
            dstep = resolve_decompose_step(
                ctx.repo_root, choice.rung, choice.target, dcfg
            )
            if dstep:
                import_step = dstep
                print(
                    f"[saturday.actions] formalize decompose_step="
                    f"{dstep.get('id')} lean_name={dstep.get('lean_name')}"
                )
                announce(
                    f"Decompose micro: {dstep.get('id')} "
                    f"({dstep.get('lean_name')})"
                )
    except Exception as exc:
        print(f"[saturday.actions] decompose_step resolve skipped: {exc}")

    try:
        from search.saturday.proof_source import (
            frontier_ns_for_module,
            load_proof_import_config,
            resolve_import_step,
        )

        if import_step is None:
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

    # Refuse model spend when theory tree is already red (shared lake pollution).
    if getattr(loop_cfg, "formalize_require_green_lake", True) and not build["ok"]:
        announce(
            "Ambient lake is red; skipping formalize model call "
            "(formalize_require_green_lake). Fix theory/ or pause the other rung."
        )
        notes = (
            "Blocked: ambient lake red before formalize. "
            + (prior_errors[-1200:] if prior_errors else "")
        )
        memory = _dated_entry("formalize", "blocked", [], notes[:500])
        return ActionResult(
            status="blocked",
            artifact_refs=[],
            notes=notes[:2000],
            next_recommended_action="formalize",
            gate_pending="none",
            memory_entry=memory,
            raw_model_text=prior_errors[-4000:],
        )

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

    from search.saturday.draft_gate import (
        build_known_ident_set,
        build_repair_context,
        is_worth_repairing,
        validate_lean_draft,
    )

    known_idents = build_known_ident_set(
        module_excerpt=module_excerpt,
        accepted_names=sel.names,
        open_obligations=open_names,
        import_step=import_step,
    )
    repair_budget = int(getattr(loop_cfg, "formalize_repair_attempts", 2) or 0)
    print(
        f"[saturday.actions] formalize repair_budget={repair_budget} "
        f"known_idents={len(known_idents)}"
    )

    remote = remote_config(loop_cfg)
    use_remote = want_remote_formalize(loop_cfg)
    remote_only = use_remote and remote.mode == "remote"

    def generate_once(
        *,
        gen_client: LocalLLMClient,
        model: str,
        api_style: str,
        tag: str,
        err_ctx: str,
        attempt: int,
    ) -> dict:
        announce(
            f"Asking {tag} model {model} for a Lean 4 Frontier draft "
            f"(attempt {attempt}, error context: {len(err_ctx)} chars)."
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
            f"frontier_ns={frontier_ns} attempt={attempt}"
        )
        resp = gen_client.generate(
            _role_request(
                loop_cfg,
                role,
                prompt,
                prompt_builders.SYSTEM_FORMALIZE,
                model_override=model,
                api_style_override=api_style,
                response_format="json_object",
            )
        )
        meta = _parse_trailing_json(resp.text)
        lean_code = _lean_from_formalize_response(resp.text, meta)
        suffix = tag if attempt <= 1 else f"{tag}_repair{attempt}"
        draft_path = _write_draft(
            ctx.repo_root,
            loop_cfg.draft_dir,
            f"{choice.rung}_formalize_{suffix}.lean",
            lean_code + "\n",
        )
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
        return {
            "lean_code": lean_code,
            "raw": resp.text,
            "meta": meta,
            "arts": arts,
            "notes": notes,
            "tag": tag,
            "model": model,
            "draft_path": draft_path,
        }

    def apply_draft(lean_code: str, arts: List[str], tag: str) -> dict:
        """Merge + lake; returns status fields (does not raise)."""
        apply_notes = "auto_apply disabled"
        status = "partial"
        gate_pending = "none"
        applied_ok = False
        build_tail = ""
        if not getattr(loop_cfg, "auto_apply", True):
            return {
                "status": status,
                "gate": gate_pending,
                "notes": " Local CLI writes drafts only; auto_apply is false.",
                "arts": arts,
                "applied_ok": False,
                "build_tail": "",
            }
        announce(
            f"Auto-apply ({tag}): merge into {lean_path.name}, lake build, "
            "revert if red."
        )
        applied = apply_frontier_draft(
            repo_root=ctx.repo_root,
            lean_path=lean_path,
            lean_code=lean_code,
            rung_id=choice.rung,
            allow_helper_only=(
                bool(import_step)
                and str(import_step.get("fill_mode") or "")
                == "helper_insert"
            ),
        )
        apply_notes = applied.notes
        build_tail = applied.build_tail or ""
        # Import micro already in theory/ but plan still pending: treat as landed.
        already_defined = (
            not applied.applied
            and "already defined" in (applied.notes or "").lower()
            and import_step
            and str(import_step.get("lean_name") or "").rsplit(".", 1)[-1]
            in (applied.notes or "")
        )
        if already_defined:
            announce(
                "Import micro already certified in theory/; advancing plan step "
                f"{import_step.get('id')} without re-apply."
            )
            try:
                from search.saturday.proof_source import (
                    entry_by_id,
                    load_proof_import_config,
                    mark_plan_step_done,
                    parse_import_cluster_target,
                )

                pi_cfg = load_proof_import_config(ctx.repo_root)
                source_id, _ = parse_import_cluster_target(choice.target)
                if not source_id:
                    source_id = str(
                        import_step.get("source_id")
                        or (pi_cfg.catalog[0].id if pi_cfg.catalog else "")
                    )
                if source_id:
                    entry = entry_by_id(pi_cfg, source_id)
                    mark_plan_step_done(
                        ctx.repo_root,
                        pi_cfg,
                        entry,
                        str(import_step.get("id")),
                        reason="already_certified",
                    )
            except Exception as exc:
                print(
                    f"[saturday.actions] already_defined mark done skipped: {exc}"
                )
            return {
                "status": "partial",
                "gate": "none",
                "notes": (
                    f" {apply_notes} plan advanced (already_certified "
                    f"{import_step.get('lean_name')})"
                ),
                "arts": arts,
                "applied_ok": True,
                "build_tail": "",
            }
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
            from search.saturday.apply_lean import extract_open_frontier_obligations

            remaining = []
            if lean_path.exists():
                remaining = extract_open_frontier_obligations(
                    lean_path.read_text(encoding="utf-8")
                )
            fill_mode = (
                str(import_step.get("fill_mode") or "") if import_step else ""
            )
            if remaining and fill_mode != "helper_insert":
                status = "partial"
                gate_pending = "none"
                announce(
                    "Apply stuck in theory/, but Frontier sorries remain: "
                    + ", ".join(remaining[:6])
                )
            elif remaining and fill_mode == "helper_insert":
                status = "partial"
                gate_pending = "none"
                announce(
                    "Import micro helper landed; Frontier sorries remain "
                    f"({len(remaining)} open)."
                )
            elif applied.has_sorry:
                status = "partial"
                gate_pending = "none"
            else:
                status = "success"
                gate_pending = "merge_certified"
            arts.append(applied.target)
            if import_step and import_step.get("id"):
                try:
                    from search.saturday.proof_source import (
                        entry_by_id,
                        load_proof_import_config,
                        mark_plan_step_done,
                        parse_import_cluster_target,
                    )

                    pi_cfg = load_proof_import_config(ctx.repo_root)
                    source_id, _ = parse_import_cluster_target(choice.target)
                    if not source_id:
                        source_id = str(
                            import_step.get("source_id")
                            or (pi_cfg.catalog[0].id if pi_cfg.catalog else "")
                        )
                    if source_id:
                        entry = entry_by_id(pi_cfg, source_id)
                        reason = (
                            "helper_insert_applied"
                            if fill_mode == "helper_insert"
                            else "formalize_applied"
                        )
                        mark_plan_step_done(
                            ctx.repo_root,
                            pi_cfg,
                            entry,
                            str(import_step.get("id")),
                            reason=reason,
                        )
                        print(
                            "[saturday.actions] import plan step marked done "
                            f"id={import_step.get('id')} reason={reason}"
                        )
                except Exception as exc:
                    print(
                        f"[saturday.actions] mark_plan_step_done skipped: {exc}"
                    )
        else:
            status = "partial"
        return {
            "status": status,
            "gate": gate_pending,
            "notes": f" {apply_notes}",
            "arts": arts,
            "applied_ok": applied_ok,
            "build_tail": build_tail,
        }

    def one_pass(
        *,
        gen_client: LocalLLMClient,
        model: str,
        api_style: str,
        tag: str,
        err_ctx: str,
    ) -> dict:
        """
        Generate -> draft_gate -> (optional) apply, with same-wake repairs.

        Pre-lake gate failures resend without lake. Close lake failures
        resend with digest when is_worth_repairing.
        """
        max_tries = 1 + max(0, repair_budget)
        cur_err = err_ctx
        last_gate = None
        outcome: Dict[str, Any] = {
            "status": "partial",
            "gate": "none",
            "notes": "no formalize attempt",
            "arts": [],
            "lean_code": "",
            "raw": "",
            "applied_ok": False,
            "build_tail": "",
            "tag": tag,
            "model": model,
        }
        all_arts: List[str] = []
        for attempt in range(1, max_tries + 1):
            print(
                f"[saturday.actions] formalize reflection attempt="
                f"{attempt}/{max_tries} tag={tag}"
            )
            gen = generate_once(
                gen_client=gen_client,
                model=model,
                api_style=api_style,
                tag=tag,
                err_ctx=cur_err,
                attempt=attempt,
            )
            all_arts = list(dict.fromkeys(all_arts + gen["arts"]))
            gate_res = validate_lean_draft(
                gen["lean_code"],
                import_step=import_step,
                known_idents=known_idents,
                meta=gen.get("meta"),
                require_known_call_sites=True,
                require_meta_decl=bool(
                    import_step
                    and str(import_step.get("fill_mode") or "") == "helper_insert"
                ),
            )
            last_gate = gate_res
            lean_code = gate_res.code
            # Persist sanitized draft for operator inspection
            if lean_code != gen["lean_code"]:
                _write_draft(
                    ctx.repo_root,
                    loop_cfg.draft_dir,
                    f"{choice.rung}_formalize_{tag}_sanitized.lean",
                    lean_code + "\n",
                )
            if not gate_res.ok:
                announce(
                    f"Draft gate rejected attempt {attempt}: "
                    + "; ".join(gate_res.reasons[:4])
                )
                outcome = {
                    "status": "partial",
                    "gate": "none",
                    "notes": (
                        f"{gen['notes']} draft_gate reject: "
                        + "; ".join(gate_res.reasons[:6])
                    ),
                    "arts": all_arts,
                    "lean_code": lean_code,
                    "raw": gen["raw"],
                    "applied_ok": False,
                    "build_tail": "",
                    "tag": tag,
                    "model": model,
                }
                if attempt < max_tries and is_worth_repairing("", gate_res):
                    cur_err = build_repair_context(
                        failed_lean=lean_code, gate=gate_res
                    )
                    announce(
                        f"Repair pass {attempt + 1}/{max_tries} "
                        "(pre-lake gate; no lake spend yet)."
                    )
                    continue
                return outcome

            applied = apply_draft(lean_code, list(all_arts), tag)
            all_arts = list(dict.fromkeys(applied["arts"]))
            outcome = {
                "status": applied["status"],
                "gate": applied["gate"],
                "notes": f"{gen['notes']}{applied['notes']}",
                "arts": all_arts,
                "lean_code": lean_code,
                "raw": gen["raw"],
                "applied_ok": applied["applied_ok"],
                "build_tail": applied["build_tail"],
                "tag": tag,
                "model": model,
            }
            if applied["applied_ok"]:
                return outcome
            if attempt < max_tries and is_worth_repairing(
                applied["build_tail"], last_gate
            ):
                cur_err = build_repair_context(
                    failed_lean=lean_code,
                    build_tail=applied["build_tail"],
                    gate=last_gate,
                )
                announce(
                    f"Repair pass {attempt + 1}/{max_tries} "
                    "(lake digest fed back)."
                )
                continue
            return outcome
        return outcome

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
                pieces.append(
                    "Local attempt outcome (reject or revert):\n" + local_notes[:2000]
                )
            local_lean = (outcome.get("lean_code") or "").strip()
            if local_lean:
                pieces.append(
                    "Local draft that failed (do not repeat its mistakes):\n"
                    + local_lean[:3000]
                )
            pieces.append(
                "Target only open Frontier obligations for this rung. "
                "Cite only identifiers from the excerpt or accepted list."
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
                remote_out["arts"] = list(
                    dict.fromkeys(outcome["arts"] + remote_out["arts"])
                )
                remote_out["notes"] = (
                    f"local:{outcome['notes'][:400]} | remote:{remote_out['notes']}"
                )
                outcome = remote_out
            except Exception as exc:
                announce(f"OpenRouter escalation failed: {exc}")
                outcome["notes"] = (
                    outcome["notes"] + f" OpenRouter escalate failed: {exc}"
                )

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
