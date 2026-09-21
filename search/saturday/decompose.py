"""
Stuck obligation decompose for satday auto.

When formalize makes no Frontier progress for N wakes, the loop:
1. Ranks accepted_declarations for the stuck obligation (reuse first).
2. Asks an LLM to propose Qwen sized micro steps that are NOT already accepted.
3. Persists a plan JSON under search/logs/decompose_plans/ (no Lean writes).

Chooser then prefers `decompose cluster: <rung> step=<id>` formalize targets.
"""

from __future__ import annotations

import json
import re
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple

from infra.config.schemas import SaturdayDecomposeConfig
from search.saturday.accepted_select import (
    load_accepted_declaration_names,
    select_accepted_declarations,
)


_JSON_FENCE = re.compile(r"```(?:json)?\s*([\s\S]*?)```", re.IGNORECASE)


@dataclass
class DecomposeResult:
    """Outcome of one decompose attempt."""

    triggered: bool = False
    plan_path: str = ""
    parent_obligation: str = ""
    reuse_names: List[str] = field(default_factory=list)
    pending_steps: int = 0
    notes: str = ""


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def plans_dir(repo_root: Path, cfg: SaturdayDecomposeConfig) -> Path:
    rel = Path(cfg.plans_dir)
    path = rel if rel.is_absolute() else Path(repo_root) / rel
    path.mkdir(parents=True, exist_ok=True)
    print(f"[saturday.decompose] plans_dir={path}")
    return path


def plan_path_for_rung(
    repo_root: Path, rung_id: str, cfg: SaturdayDecomposeConfig
) -> Path:
    return plans_dir(repo_root, cfg) / f"{rung_id}.json"


def load_decompose_plan(
    repo_root: Path, rung_id: str, cfg: SaturdayDecomposeConfig
) -> Optional[Dict[str, Any]]:
    path = plan_path_for_rung(repo_root, rung_id, cfg)
    if not path.is_file():
        print(f"[saturday.decompose] no plan at {path}")
        return None
    try:
        plan = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"[saturday.decompose] bad plan JSON: {exc}")
        return None
    print(
        f"[saturday.decompose] loaded plan steps={len(plan.get('steps') or [])} "
        f"parent={plan.get('parent_obligation')!r}"
    )
    return plan


def save_decompose_plan(
    repo_root: Path,
    rung_id: str,
    plan: Dict[str, Any],
    cfg: SaturdayDecomposeConfig,
) -> Path:
    path = plan_path_for_rung(repo_root, rung_id, cfg)
    plan["updated_at"] = _now_iso()
    path.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
    print(f"[saturday.decompose] saved plan {path}")
    return path


def next_decompose_step(plan: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    for step in plan.get("steps") or []:
        if str(step.get("status", "pending")) != "done":
            return step
    return None


def has_pending_decompose(
    repo_root: Path, rung_id: str, cfg: SaturdayDecomposeConfig
) -> bool:
    plan = load_decompose_plan(repo_root, rung_id, cfg)
    if plan is None:
        return False
    return next_decompose_step(plan) is not None


def accepted_short_name_set(repo_root: Path, decls_path: str) -> Set[str]:
    """Short and FQ names from the axiom gate allowlist."""
    path = Path(decls_path)
    if not path.is_absolute():
        path = Path(repo_root) / path
    names = load_accepted_declaration_names(path)
    out: Set[str] = set()
    for fq in names:
        out.add(fq)
        out.add(fq.rsplit(".", 1)[-1])
    print(f"[saturday.decompose] accepted name set size={len(out)}")
    return out


def mark_already_accepted_steps(
    plan: Dict[str, Any], accepted: Set[str]
) -> int:
    """Flip pending steps whose lean_name is already in accepted decls."""
    marked = 0
    for step in plan.get("steps") or []:
        if str(step.get("status", "pending")) == "done":
            continue
        lean_name = str(step.get("lean_name") or "")
        short = lean_name.rsplit(".", 1)[-1]
        if lean_name in accepted or short in accepted:
            step["status"] = "done"
            step["done_reason"] = "already_accepted"
            step["done_at"] = _now_iso()
            marked += 1
            print(
                f"[saturday.decompose] step {step.get('id')} already_accepted "
                f"lean_name={lean_name}"
            )
    return marked


def auto_advance_certified_decompose(
    repo_root: Path, plan: Dict[str, Any]
) -> int:
    """Mark pending micros done when lean_name is certified (non-sorry) in module."""
    from search.saturday.proof_source import lean_name_is_certified

    advanced = 0
    for step in plan.get("steps") or []:
        if str(step.get("status", "pending")) == "done":
            continue
        lean_name = str(step.get("lean_name") or "")
        module = str(step.get("module") or "")
        if not lean_name or not module:
            continue
        path = Path(repo_root) / module
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        if lean_name_is_certified(text, lean_name):
            step["status"] = "done"
            step["done_reason"] = "already_certified"
            step["done_at"] = _now_iso()
            advanced += 1
            print(
                f"[saturday.decompose] auto_advance certified "
                f"step={step.get('id')} lean_name={lean_name}"
            )
    return advanced


def parse_decompose_target(target: str) -> Tuple[Optional[str], Optional[str]]:
    """Parse `decompose cluster: <rung_id> step=<step_id>`."""
    t = (target or "").strip()
    lower = t.lower()
    rung_id: Optional[str] = None
    step_id: Optional[str] = None
    if lower.startswith("decompose cluster:"):
        rest = t[len("decompose cluster:") :].strip()
        parts = rest.split()
        if parts:
            rung_id = parts[0].strip()
        for p in parts[1:]:
            if p.lower().startswith("step="):
                step_id = p.split("=", 1)[1].strip()
                break
    print(
        f"[saturday.decompose] parse_decompose_target "
        f"rung_id={rung_id!r} step_id={step_id!r}"
    )
    return rung_id, step_id


def is_decompose_target(target: str) -> bool:
    return (target or "").strip().lower().startswith("decompose cluster:")


def resolve_decompose_step(
    repo_root: Path,
    rung_id: str,
    target: str,
    cfg: Optional[SaturdayDecomposeConfig] = None,
) -> Optional[Dict[str, Any]]:
    """Return the plan step dict for a decompose formalize target."""
    cfg = cfg or SaturdayDecomposeConfig()
    if not is_decompose_target(target):
        return None
    parsed_rung, step_id = parse_decompose_target(target)
    use_rung = parsed_rung or rung_id
    plan = load_decompose_plan(repo_root, use_rung, cfg)
    if plan is None:
        return None
    accepted_cfg_path = "scripts/accepted_declarations.txt"
    accepted = accepted_short_name_set(repo_root, accepted_cfg_path)
    changed = mark_already_accepted_steps(plan, accepted)
    changed += auto_advance_certified_decompose(repo_root, plan)
    if changed:
        save_decompose_plan(repo_root, use_rung, plan, cfg)
    if step_id:
        for step in plan.get("steps") or []:
            if str(step.get("id") or "") == step_id:
                print(f"[saturday.decompose] resolve step_id={step_id}")
                return step
        print(f"[saturday.decompose] resolve miss step_id={step_id!r}")
        return None
    step = next_decompose_step(plan)
    print(
        f"[saturday.decompose] resolve next "
        f"step={None if not step else step.get('id')}"
    )
    return step


def suggest_decompose_action(
    repo_root: Path,
    rung_id: str,
    cfg: Optional[SaturdayDecomposeConfig] = None,
) -> Optional[Tuple[str, str, str]]:
    """
    If a decompose plan has a pending micro, return formalize target triple.
    """
    cfg = cfg or SaturdayDecomposeConfig()
    if not cfg.enabled:
        print("[saturday.decompose] suggest disabled")
        return None
    plan = load_decompose_plan(repo_root, rung_id, cfg)
    if plan is None:
        return None
    accepted = accepted_short_name_set(
        repo_root, "scripts/accepted_declarations.txt"
    )
    changed = mark_already_accepted_steps(plan, accepted)
    changed += auto_advance_certified_decompose(repo_root, plan)
    if changed:
        save_decompose_plan(repo_root, rung_id, plan, cfg)
    step = next_decompose_step(plan)
    if step is None:
        print("[saturday.decompose] suggest: no pending steps")
        return None
    step_id = str(step.get("id") or "next")
    target = f"decompose cluster: {rung_id} step={step_id}"
    rationale = (
        f"Decompose plan pending micro {step_id} "
        f"lean_name={step.get('lean_name')} "
        f"(parent={plan.get('parent_obligation')})"
    )
    print(f"[saturday.decompose] suggest formalize target={target!r}")
    return "formalize", target, rationale


def _extract_json_obj(text: str) -> Optional[Dict[str, Any]]:
    raw = (text or "").strip()
    if not raw:
        return None
    fence = _JSON_FENCE.search(raw)
    if fence:
        raw = fence.group(1).strip()
    try:
        obj = json.loads(raw)
        if isinstance(obj, dict):
            return obj
    except Exception:
        pass
    # Find first { ... } blob
    start = raw.find("{")
    end = raw.rfind("}")
    if start >= 0 and end > start:
        try:
            obj = json.loads(raw[start : end + 1])
            if isinstance(obj, dict):
                return obj
        except Exception as exc:
            print(f"[saturday.decompose] JSON parse failed: {exc}")
    return None


def _build_reuse_only_plan(
    *,
    rung_id: str,
    parent: str,
    module: str,
    reuse: Sequence[Tuple[str, float]],
    max_steps: int,
) -> Dict[str, Any]:
    """Deterministic plan when LLM is unavailable: reuse accepted, then glue parent."""
    steps: List[Dict[str, Any]] = []
    for i, (fq, score) in enumerate(reuse[: max(0, max_steps - 1)]):
        short = fq.rsplit(".", 1)[-1]
        steps.append(
            {
                "id": f"reuse-{i}-{short}"[:80],
                "status": "done",
                "unit": "micro",
                "lean_name": short,
                "lean_sig": f"(accepted) {fq}",
                "module": module,
                "allowed_tactics": ["exact", "apply"],
                "fill_mode": "sorry_replace",
                "goal": f"Already accepted subcomponent score={score:.1f}",
                "done_reason": "already_accepted",
                "done_at": _now_iso(),
            }
        )
    reuse_shorts = [fq.rsplit(".", 1)[-1] for fq, _ in reuse[:12]]
    steps.append(
        {
            "id": "glue-parent",
            "status": "pending",
            "unit": "micro",
            "lean_name": parent,
            "lean_sig": f"Discharge {parent} via exact/apply of reuse list",
            "module": module,
            "allowed_tactics": ["exact", "apply", "intro", "refine", "have"],
            "fill_mode": "sorry_replace",
            "max_chars": 4000,
            "goal": (
                "Close the stuck Frontier obligation using already accepted "
                f"decls: {', '.join(reuse_shorts) or '(none)'}. Do not invent "
                "new spectral analysis."
            ),
            "reuse_names": reuse_shorts,
        }
    )
    return {
        "rung_id": rung_id,
        "parent_obligation": parent,
        "method": "accepted_reuse_only",
        "created_at": _now_iso(),
        "steps": steps,
    }


def _normalize_llm_steps(
    raw_steps: Sequence[Any],
    *,
    parent: str,
    module: str,
    max_steps: int,
) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for i, item in enumerate(raw_steps or []):
        if len(out) >= max_steps:
            break
        if not isinstance(item, dict):
            continue
        lean_name = str(item.get("lean_name") or "").strip()
        if not lean_name:
            continue
        sid = str(item.get("id") or f"micro-{i}-{lean_name}")[:80]
        tactics = item.get("allowed_tactics") or [
            "decide",
            "omega",
            "simp",
            "rfl",
            "exact",
            "apply",
        ]
        out.append(
            {
                "id": sid,
                "status": "pending",
                "unit": str(item.get("unit") or "micro"),
                "lean_name": lean_name,
                "lean_sig": str(item.get("lean_sig") or item.get("goal") or ""),
                "module": str(item.get("module") or module),
                "allowed_tactics": [str(t) for t in tactics][:12],
                "fill_mode": str(item.get("fill_mode") or "sorry_replace"),
                "max_chars": int(item.get("max_chars") or 4000),
                "goal": str(item.get("goal") or ""),
                "parent_obligation": parent,
            }
        )
    return out


def build_decompose_prompt(
    *,
    rung_id: str,
    parent: str,
    module_excerpt: str,
    accepted_block: str,
    reuse_names: Sequence[str],
    max_micro_steps: int,
) -> str:
    reuse_s = ", ".join(reuse_names) if reuse_names else "(none ranked high)"
    return f"""Rung id: {rung_id}
Stuck Frontier obligation: {parent}

You are the saturday loop decompose planner. Formalize has stalled on a lemma
that is too large for one wake. Propose a micro lemma ladder.

Rules:
1. First, treat the accepted declarations below as already proven. Never propose
   a new micro whose lean_name matches an accepted declaration.
2. Prefer exact or apply reuse of those accepted names for glue steps.
3. Only invent NEW micro lemmas when a subgoal is missing from accepted decls.
4. Each micro must be Qwen sized: one named lemma, fixed tactics
   (decide, omega, simp, rfl, exact, apply), fill only the by block.
5. Do not write Lean code. Do not invent AFP axioms. Output JSON only.
6. Never use hyphens as punctuation; use spaces or commas in prose fields.
7. At most {max_micro_steps} steps. Order dependencies first.

Accepted declarations (smart select; already proven):
{accepted_block}

High score reuse candidates: {reuse_s}

Lean excerpt (truncated):
{(module_excerpt or '')[:8000]}

Return JSON shaped exactly like:
{{
  "parent_obligation": "{parent}",
  "notes": "one sentence",
  "steps": [
    {{
      "id": "micro-1",
      "lean_name": "shortLemmaName",
      "lean_sig": "theorem shortLemmaName ...",
      "goal": "what this micro discharges",
      "allowed_tactics": ["decide", "omega"],
      "unit": "micro",
      "fill_mode": "sorry_replace",
      "max_chars": 4000
    }}
  ]
}}
"""


def run_decompose(
    repo_root: Path,
    *,
    rung_id: str,
    obligations: Sequence[str],
    module_path: str,
    module_excerpt: str = "",
    loop_cfg: Any = None,
    client: Any = None,
    cfg: Optional[SaturdayDecomposeConfig] = None,
) -> DecomposeResult:
    """
    Build or refresh a decompose plan for the first open obligation.

    Does not write Lean. Always ranks accepted decls before any LLM call.
    """
    cfg = cfg or getattr(loop_cfg, "decompose", None) or SaturdayDecomposeConfig()
    result = DecomposeResult()
    if not cfg.enabled:
        result.notes = "decompose disabled"
        print(f"[saturday.decompose] {result.notes}")
        return result
    if not obligations:
        result.notes = "no open obligations to decompose"
        print(f"[saturday.decompose] {result.notes}")
        return result

    parent = str(obligations[0])
    result.parent_obligation = parent
    print(
        f"[saturday.decompose] run rung={rung_id} parent={parent} "
        f"module={module_path}"
    )

    # Skip rebuild when pending micros already exist for same parent, unless
    # the plan is a reuse-only glue stub and we now have an LLM to split further.
    existing = load_decompose_plan(repo_root, rung_id, cfg)
    if existing and existing.get("parent_obligation") == parent:
        pending = next_decompose_step(existing)
        if pending is not None:
            refresh_glue = (
                existing.get("method") == "accepted_reuse_only"
                and str(pending.get("id") or "") == "glue-parent"
                and client is not None
            )
            if not refresh_glue:
                result.triggered = False
                result.plan_path = str(plan_path_for_rung(repo_root, rung_id, cfg))
                result.pending_steps = sum(
                    1
                    for s in (existing.get("steps") or [])
                    if str(s.get("status")) != "done"
                )
                result.notes = "existing pending decompose plan retained"
                print(f"[saturday.decompose] {result.notes}")
                return result
            print(
                "[saturday.decompose] refreshing accepted_reuse_only glue "
                "with LLM micro split"
            )

    sel_cfg = getattr(loop_cfg, "accepted_select", None) if loop_cfg else None
    sel = select_accepted_declarations(
        repo_root,
        rung_id=rung_id,
        target=f"decompose {parent}",
        open_obligations=[parent],
        module_excerpt=module_excerpt,
        cfg=sel_cfg,
    )
    min_score = float(cfg.min_accepted_reuse_score)
    reuse = [
        (fq, sel.scores.get(fq, 0.0))
        for fq in sel.names
        if sel.scores.get(fq, 0.0) >= min_score
    ]
    result.reuse_names = [fq.rsplit(".", 1)[-1] for fq, _ in reuse]
    print(
        f"[saturday.decompose] accepted reuse hits={len(reuse)} "
        f"min_score={min_score} names={result.reuse_names[:8]}"
    )

    accepted_block = sel.format_block(max_chars=3500)
    plan: Optional[Dict[str, Any]] = None

    if client is not None:
        from search.llm.client import LLMRequest
        from search.saturday.prompts import SYSTEM_FORMALIZE

        role = getattr(loop_cfg, "formalize", None) if loop_cfg else None
        model = getattr(role, "model", None) or "qwen2.5-coder:14b"
        # Prefer remote formalize model when client is openrouter
        remote = getattr(loop_cfg, "remote", None) if loop_cfg else None
        if getattr(client, "label", "") == "openrouter" and remote is not None:
            model = getattr(remote, "formalize_model", None) or model
        prompt = build_decompose_prompt(
            rung_id=rung_id,
            parent=parent,
            module_excerpt=module_excerpt,
            accepted_block=accepted_block,
            reuse_names=result.reuse_names,
            max_micro_steps=cfg.max_micro_steps,
        )
        print(
            f"[saturday.decompose] LLM propose model={model} "
            f"prompt_chars={len(prompt)}"
        )
        try:
            resp = client.generate(
                LLMRequest(
                    model=model,
                    prompt=prompt,
                    system=SYSTEM_FORMALIZE
                    + " You emit JSON plans only. Never emit Lean. Never use "
                    "hyphens as punctuation.",
                    temperature=0.1,
                    num_predict=4096,
                    api_style=getattr(client, "api_style", "ollama"),
                )
            )
            parsed = _extract_json_obj(resp.text)
            if parsed:
                steps = _normalize_llm_steps(
                    parsed.get("steps") or [],
                    parent=parent,
                    module=module_path,
                    max_steps=cfg.max_micro_steps,
                )
                plan = {
                    "rung_id": rung_id,
                    "parent_obligation": parent,
                    "method": "llm_micro_split",
                    "created_at": _now_iso(),
                    "notes": str(parsed.get("notes") or ""),
                    "reuse_names": result.reuse_names,
                    "steps": steps,
                }
                print(
                    f"[saturday.decompose] LLM returned steps={len(steps)} "
                    f"notes={plan.get('notes')!r}"
                )
            else:
                print("[saturday.decompose] LLM response lacked JSON object")
        except Exception as exc:
            print(f"[saturday.decompose] LLM propose failed: {exc}")

    if plan is None or not (plan.get("steps") or []):
        print("[saturday.decompose] falling back to accepted_reuse_only plan")
        plan = _build_reuse_only_plan(
            rung_id=rung_id,
            parent=parent,
            module=module_path,
            reuse=reuse,
            max_steps=cfg.max_micro_steps,
        )

    accepted = accepted_short_name_set(
        repo_root,
        getattr(sel_cfg, "decls_path", None) or "scripts/accepted_declarations.txt",
    )
    # Never leave a pending micro that is already accepted (except parent glue)
    for step in plan.get("steps") or []:
        lean_name = str(step.get("lean_name") or "")
        short = lean_name.rsplit(".", 1)[-1]
        parent_short = parent.rsplit(".", 1)[-1]
        if short == parent_short or lean_name == parent:
            continue
        if lean_name in accepted or short in accepted:
            step["status"] = "done"
            step["done_reason"] = "already_accepted"
            step["done_at"] = _now_iso()
    mark_already_accepted_steps(plan, accepted)
    auto_advance_certified_decompose(repo_root, plan)

    path = save_decompose_plan(repo_root, rung_id, plan, cfg)
    result.triggered = True
    try:
        result.plan_path = str(path.relative_to(repo_root))
    except ValueError:
        result.plan_path = str(path)
    result.pending_steps = sum(
        1 for s in (plan.get("steps") or []) if str(s.get("status")) != "done"
    )
    result.notes = (
        f"decompose plan parent={parent} pending={result.pending_steps} "
        f"reuse={len(result.reuse_names)} method={plan.get('method')}"
    )
    print(f"[saturday.decompose] {result.notes}")
    return result


def maybe_decompose_after_reflect(
    repo_root: Path,
    *,
    rung_id: str,
    wakes_without_progress: int,
    obligations: Sequence[str],
    module_path: str,
    module_excerpt: str,
    loop_cfg: Any,
    client: Any = None,
) -> Optional[DecomposeResult]:
    """Hook: run decompose when reflect counters cross the trigger."""
    cfg = getattr(loop_cfg, "decompose", None) or SaturdayDecomposeConfig()
    if not cfg.enabled:
        return None
    if wakes_without_progress < int(cfg.trigger_after_wakes):
        print(
            f"[saturday.decompose] skip trigger wakes={wakes_without_progress} "
            f"< {cfg.trigger_after_wakes}"
        )
        return None
    print(
        f"[saturday.decompose] trigger wakes={wakes_without_progress} "
        f">= {cfg.trigger_after_wakes}"
    )
    return run_decompose(
        repo_root,
        rung_id=rung_id,
        obligations=obligations,
        module_path=module_path,
        module_excerpt=module_excerpt,
        loop_cfg=loop_cfg,
        client=client,
        cfg=cfg,
    )
