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
    prompt = prompt_builders.build_prove_prompt(ctx, choice)
    print(f"[saturday.actions] prove model={role.model}")
    resp = client.generate(_role_request(loop_cfg, role, prompt, prompt_builders.SYSTEM_PROVE))
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
        f"{choice.rung}_prove.md",
        resp.text,
    )
    memory = _dated_entry(
        "prove",
        status,
        [artifact, str(prose_path.relative_to(ctx.repo_root))],
        notes[:500],
    )
    # Also append the prose body into memory under the dated entry
    memory = memory + "\n\n" + truncate_for_prompt(resp.text, 8000)
    return ActionResult(
        status=status,
        artifact_refs=[artifact, str(prose_path.relative_to(ctx.repo_root))],
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
    """Map rung id to a primary Lean file under theory/."""
    mapping = {
        "r0-resolution-foundations": "theory/Theory/ProofComplexity/Resolution.lean",
        "r1-php-haken": "theory/Theory/ProofComplexity/PHP.lean",
        # R2 critical path lives in CSExpansionFrontier, not Width.lean
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
    from search.saturday.llm_factory import (
        make_remote_client,
        remote_config,
        want_remote_formalize,
    )

    role = loop_cfg.formalize
    lean_path = _guess_lean_target(ctx, choice)
    module_excerpt = ""
    open_obs = ""
    if lean_path.exists():
        from search.saturday.apply_lean import extract_open_frontier_obligations

        full = lean_path.read_text(encoding="utf-8")
        module_excerpt = _frontier_focus_excerpt(full)
        names = extract_open_frontier_obligations(module_excerpt)
        if not names:
            names = extract_open_frontier_obligations(full)
        open_obs = "\n".join(f"- {n}" for n in names) if names else ""
        print(f"[saturday.actions] open Frontier obligations={names}")
        if names:
            announce(
                f"Open Frontier obligations for {choice.rung}: " + ", ".join(names)
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
                if applied.has_sorry:
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
        rclient = make_remote_client(loop_cfg)
        outcome = one_pass(
            gen_client=rclient,
            model=remote.formalize_model,
            api_style=remote.api_style,
            tag="openrouter",
            err_ctx=prior_errors,
        )
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
