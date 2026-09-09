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
) -> LLMRequest:
    return LLMRequest(
        model=role.model,
        prompt=prompt,
        system=system,
        temperature=role.temperature,
        num_predict=role.num_predict,
        api_style=loop_cfg.api_style,
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
        "r2-width-machinery": "theory/Theory/ProofComplexity/Width.lean",
        "r3-stronger-systems": "theory/Theory/ProofComplexity/Resolution.lean",
        "r4-frontier": "theory/Theory/ProofComplexity/Width.lean",
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

    role = loop_cfg.formalize
    lean_path = _guess_lean_target(ctx, choice)
    module_excerpt = ""
    if lean_path.exists():
        module_excerpt = lean_path.read_text(encoding="utf-8")[-12000:]
    else:
        module_excerpt = f"(missing file {lean_path})"

    build = lake_build_locked(ctx.repo_root)
    prior_errors = "" if build["ok"] else build["output"][-6000:]
    print(f"[saturday.actions] formalize ambient_build_ok={build['ok']}")

    print(f"[saturday.actions] formalize model={role.model}")
    prompt = prompt_builders.build_formalize_prompt(
        ctx, choice, module_excerpt, prior_errors=prior_errors
    )
    resp = client.generate(
        _role_request(loop_cfg, role, prompt, prompt_builders.SYSTEM_FORMALIZE)
    )
    fence = LEAN_FENCE_RE.search(resp.text)
    lean_code = fence.group(1).strip() if fence else resp.text
    draft_path = _write_draft(
        ctx.repo_root,
        loop_cfg.draft_dir,
        f"{choice.rung}_formalize.lean",
        lean_code + "\n",
    )
    meta = _parse_trailing_json(resp.text)
    next_action = str(meta.get("next_recommended_action", "formalize"))
    if next_action not in {"prove", "formalize", "falsify", "audit"}:
        print(
            f"[saturday.actions] sanitize formalize next_recommended_action "
            f"from {next_action!r} to formalize"
        )
        next_action = "formalize"

    arts = [
        str(draft_path.relative_to(ctx.repo_root)),
        str(lean_path.relative_to(ctx.repo_root)) if lean_path.exists() else "",
    ]
    arts = [a for a in arts if a]
    notes = str(meta.get("notes") or f"Lean draft at {draft_path.relative_to(ctx.repo_root)}")

    apply_notes = "auto_apply disabled"
    status = "partial"
    gate = "none"
    if getattr(loop_cfg, "auto_apply", True):
        print(f"[saturday.actions] auto_apply enabled for {choice.rung}")
        applied = apply_frontier_draft(
            repo_root=ctx.repo_root,
            lean_path=lean_path,
            lean_code=lean_code,
            rung_id=choice.rung,
        )
        apply_notes = applied.notes
        if applied.build_tail:
            # Persist compile errors for the next formalize wake
            err_draft = _write_draft(
                ctx.repo_root,
                loop_cfg.draft_dir,
                f"{choice.rung}_apply_error.txt",
                applied.build_tail,
            )
            arts.append(str(err_draft.relative_to(ctx.repo_root)))
        if applied.applied and applied.build_ok:
            if applied.has_sorry:
                status = "partial"
                gate = "none"
                next_action = "formalize"
            else:
                status = "success"
                gate = "merge_certified"
                next_action = "formalize"
            arts.append(applied.target)
        elif applied.reverted:
            status = "partial"
            next_action = "formalize"
        else:
            status = "partial"
    else:
        notes = notes + " Local CLI writes drafts only; auto_apply is false."

    notes = f"{notes} {apply_notes}"
    if not build["ok"]:
        notes = notes + f" Ambient lake build was red (tail): {prior_errors[-800:]}"

    memory = _dated_entry("formalize", status, arts, notes[:500])
    memory = memory + "\n\n" + truncate_for_prompt(lean_code, 4000)
    return ActionResult(
        status=status,
        artifact_refs=arts,
        notes=notes[:2000],
        next_recommended_action=next_action,
        gate_pending=gate,
        memory_entry=memory,
        raw_model_text=resp.text,
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


def _write_draft(repo_root: Path, draft_dir: str, name: str, content: str) -> Path:
    """Write a draft artifact under search/logs/saturday_drafts."""
    directory = repo_root / draft_dir
    directory.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    path = directory / f"{stamp}_{name}"
    path.write_text(content, encoding="utf-8")
    print(f"[saturday.actions] draft written path={path} bytes={len(content)}")
    return path
