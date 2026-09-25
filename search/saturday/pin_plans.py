"""Pin plans: per-rung control plane for saturday chooser routing.

Persists pin health, checklist steps, and pause metadata under
``search/logs/pin_plans/<rung_id>.json`` so the loop can refuse dead
formalize targets and prefer ``ready_for_auto`` checklist steps.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

PIN_STATUSES = frozenset(
    {
        "live",
        "dead",
        "restated",
        "archival",
        "done",
        "blocked_missing_surface",
    }
)
CHECKLIST_STATUSES = frozenset(
    {
        "pending",
        "ready_for_auto",
        "in_progress",
        "done",
        "blocked",
        "skipped",
    }
)
FORMALIZE_REFUSE_PIN_STATUSES = frozenset(
    {"dead", "archival", "blocked_missing_surface", "done", "restated"}
)

# Alias short labels used in docs to ladder memory ids.
RUNG_ALIASES = {
    "R2": "r2-width-machinery",
    "r2": "r2-width-machinery",
    "R5": "r5-cook-reckhow-bridge",
    "r5": "r5-cook-reckhow-bridge",
}


def normalize_rung_id(rung_id: str) -> str:
    raw = str(rung_id or "").strip()
    return RUNG_ALIASES.get(raw, raw)


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def pin_plans_dir(repo_root: Path) -> Path:
    return Path(repo_root) / "search" / "logs" / "pin_plans"


def pin_plan_path(repo_root: Path, rung_id: str) -> Path:
    rid = normalize_rung_id(rung_id)
    safe = "".join(ch if ch.isalnum() or ch in "-_." else "_" for ch in rid)
    return pin_plans_dir(repo_root) / f"{safe}.json"


def empty_pin_plan(rung_id: str) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "rung_id": normalize_rung_id(rung_id),
        "updated_at": _utc_now(),
        "paused": False,
        "pause_reason": "",
        "ambient_red_streak": 0,
        "checklist_ref": "",
        "pins": [],
        "checklist": [],
        "notes": [],
    }


def load_pin_plan(repo_root: Path, rung_id: str) -> dict[str, Any]:
    rid = normalize_rung_id(rung_id)
    path = pin_plan_path(repo_root, rid)
    if not path.is_file():
        return empty_pin_plan(rid)
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        return empty_pin_plan(rid)
    plan = empty_pin_plan(rid)
    plan.update(raw)
    plan["rung_id"] = normalize_rung_id(str(plan.get("rung_id") or rid))
    plan["paused"] = bool(plan.get("paused", False))
    plan["pause_reason"] = str(plan.get("pause_reason") or "")
    plan["ambient_red_streak"] = int(plan.get("ambient_red_streak") or 0)
    plan["pins"] = list(plan.get("pins") or [])
    plan["checklist"] = list(plan.get("checklist") or [])
    plan["notes"] = list(plan.get("notes") or [])
    return plan


def save_pin_plan(repo_root: Path, plan: dict[str, Any]) -> Path:
    rid = normalize_rung_id(str(plan.get("rung_id") or "unknown"))
    plan = dict(plan)
    plan["rung_id"] = rid
    path = pin_plan_path(repo_root, rid)
    path.parent.mkdir(parents=True, exist_ok=True)
    plan["updated_at"] = _utc_now()
    plan["schema_version"] = int(plan.get("schema_version") or 1)
    path.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[saturday.pin_plans] saved path={path} paused={plan.get('paused')}")
    return path


def is_rung_paused(repo_root: Path, rung_id: str) -> bool:
    return bool(load_pin_plan(repo_root, rung_id).get("paused"))


def pause_rung_plan(repo_root: Path, rung_id: str, reason: str) -> Path:
    plan = load_pin_plan(repo_root, rung_id)
    plan["paused"] = True
    plan["pause_reason"] = str(reason or "paused")
    plan.setdefault("notes", []).append(
        {"at": _utc_now(), "kind": "pause", "text": str(reason or "paused")}
    )
    return save_pin_plan(repo_root, plan)


def unpause_rung_plan(
    repo_root: Path, rung_id: str, reason: str = "operator_unpause"
) -> Path:
    plan = load_pin_plan(repo_root, rung_id)
    plan["paused"] = False
    plan["pause_reason"] = ""
    plan.setdefault("notes", []).append(
        {"at": _utc_now(), "kind": "unpause", "text": str(reason or "operator_unpause")}
    )
    return save_pin_plan(repo_root, plan)


def set_ambient_red_streak(repo_root: Path, rung_id: str, streak: int) -> Path:
    plan = load_pin_plan(repo_root, rung_id)
    plan["ambient_red_streak"] = max(0, int(streak))
    return save_pin_plan(repo_root, plan)


def bump_ambient_red_streak(repo_root: Path, rung_id: str) -> int:
    plan = load_pin_plan(repo_root, rung_id)
    streak = int(plan.get("ambient_red_streak") or 0) + 1
    plan["ambient_red_streak"] = streak
    save_pin_plan(repo_root, plan)
    print(f"[saturday.pin_plans] ambient_red_streak rung={rung_id} -> {streak}")
    return streak


def clear_ambient_red_streak(repo_root: Path, rung_id: str) -> Path:
    return set_ambient_red_streak(repo_root, rung_id, 0)


def find_pin(plan: dict[str, Any], pin_id: str) -> dict[str, Any] | None:
    for pin in plan.get("pins") or []:
        if isinstance(pin, dict) and str(pin.get("id") or "") == pin_id:
            return pin
    return None


def find_checklist_step(plan: dict[str, Any], step_id: str) -> dict[str, Any] | None:
    for step in plan.get("checklist") or []:
        if isinstance(step, dict) and str(step.get("id") or "") == step_id:
            return step
    return None


def set_pin_status(
    repo_root: Path,
    rung_id: str,
    pin_id: str,
    status: str,
    *,
    reason: str = "",
    create_if_missing: bool = False,
) -> Path:
    status_n = str(status or "").strip().lower()
    if status_n not in PIN_STATUSES:
        raise ValueError(f"invalid pin status: {status!r}; expected one of {sorted(PIN_STATUSES)}")
    plan = load_pin_plan(repo_root, rung_id)
    pin = find_pin(plan, pin_id)
    if pin is None:
        if not create_if_missing:
            raise KeyError(f"pin {pin_id!r} not found in plan for {rung_id}")
        pin = {
            "id": pin_id,
            "title": pin_id,
            "status": status_n,
            "lean_decl": "",
            "method_family": "",
            "ready_for_auto": False,
            "notes": "",
        }
        plan.setdefault("pins", []).append(pin)
    pin["status"] = status_n
    if reason:
        pin["notes"] = str(reason)
    plan.setdefault("notes", []).append(
        {
            "at": _utc_now(),
            "kind": "pin_status",
            "pin_id": pin_id,
            "status": status_n,
            "text": str(reason or ""),
        }
    )
    return save_pin_plan(repo_root, plan)


def set_checklist_status(
    repo_root: Path,
    rung_id: str,
    step_id: str,
    status: str,
    *,
    reason: str = "",
) -> Path:
    status_n = str(status or "").strip().lower()
    if status_n not in CHECKLIST_STATUSES:
        raise ValueError(
            f"invalid checklist status: {status!r}; expected one of {sorted(CHECKLIST_STATUSES)}"
        )
    plan = load_pin_plan(repo_root, rung_id)
    step = find_checklist_step(plan, step_id)
    if step is None:
        raise KeyError(f"checklist step {step_id!r} not found in plan for {rung_id}")
    step["status"] = status_n
    if reason:
        step["notes"] = str(reason)
    plan.setdefault("notes", []).append(
        {
            "at": _utc_now(),
            "kind": "checklist_status",
            "step_id": step_id,
            "status": status_n,
            "text": str(reason or ""),
        }
    )
    return save_pin_plan(repo_root, plan)


def next_ready_checklist_step(plan: dict[str, Any]) -> dict[str, Any] | None:
    for step in plan.get("checklist") or []:
        if not isinstance(step, dict):
            continue
        if str(step.get("status") or "").lower() == "ready_for_auto":
            return step
    return None


def next_live_auto_pin(plan: dict[str, Any]) -> dict[str, Any] | None:
    for pin in plan.get("pins") or []:
        if not isinstance(pin, dict):
            continue
        status = str(pin.get("status") or "").lower()
        if status != "live":
            continue
        if not bool(pin.get("ready_for_auto", False)):
            continue
        return pin
    return None


def pin_status_for_decl(plan: dict[str, Any], lean_decl: str) -> str | None:
    needle = str(lean_decl or "").strip()
    if not needle:
        return None
    short = needle.rsplit(".", 1)[-1]
    for pin in plan.get("pins") or []:
        if not isinstance(pin, dict):
            continue
        decl = str(pin.get("lean_decl") or "").strip()
        if decl and (decl == needle or decl.rsplit(".", 1)[-1] == short):
            return str(pin.get("status") or "").lower() or None
        if str(pin.get("id") or "").strip() == needle:
            return str(pin.get("status") or "").lower() or None
    return None


def formalize_refused_for_pin(
    plan: dict[str, Any], lean_decl: str
) -> tuple[bool, str]:
    status = pin_status_for_decl(plan, lean_decl)
    if status is None:
        return False, ""
    if status in FORMALIZE_REFUSE_PIN_STATUSES:
        return True, f"pin_status_{status}"
    return False, ""


def routing_hint(repo_root: Path, rung_id: str) -> dict[str, Any]:
    """Compact hint for chooser / session records."""
    plan = load_pin_plan(repo_root, rung_id)
    step = next_ready_checklist_step(plan)
    pin = next_live_auto_pin(plan)
    return {
        "rung_id": normalize_rung_id(rung_id),
        "paused": bool(plan.get("paused")),
        "pause_reason": str(plan.get("pause_reason") or ""),
        "ambient_red_streak": int(plan.get("ambient_red_streak") or 0),
        "checklist_ref": str(plan.get("checklist_ref") or ""),
        "next_checklist_id": str(step.get("id") or "") if step else "",
        "next_checklist_action": str(step.get("preferred_action") or "") if step else "",
        "next_checklist_title": str(step.get("title") or "") if step else "",
        "next_live_pin_id": str(pin.get("id") or "") if pin else "",
        "next_live_pin_decl": str(pin.get("lean_decl") or "") if pin else "",
        "pin_count": len(plan.get("pins") or []),
        "checklist_count": len(plan.get("checklist") or []),
    }


def ensure_seed_plan(repo_root: Path, rung_id: str, seed: dict[str, Any]) -> Path:
    """Write seed if missing; leave existing plans untouched."""
    path = pin_plan_path(repo_root, rung_id)
    if path.is_file():
        return path
    plan = empty_pin_plan(rung_id)
    for key in ("checklist_ref", "pins", "checklist", "notes", "paused", "pause_reason"):
        if key in seed:
            plan[key] = seed[key]
    return save_pin_plan(repo_root, plan)


def suggest_pin_plan_action(
    repo_root: Path, rung_id: str
) -> tuple[str, str, str] | None:
    """
    Return (action, target, rationale) from pin plan, or None.

    Prefer ready_for_auto checklist steps, then live ready_for_auto pins.
    """
    plan = load_pin_plan(repo_root, rung_id)
    if plan.get("paused"):
        print(
            f"[saturday.pin_plans] rung={rung_id} paused "
            f"reason={plan.get('pause_reason')!r}"
        )
        return None
    step = next_ready_checklist_step(plan)
    if step is not None:
        action = str(step.get("preferred_action") or "audit").strip().lower()
        if action not in {"prove", "formalize", "falsify", "audit"}:
            action = "audit"
        title = str(step.get("title") or step.get("id") or "checklist")
        target = str(step.get("target") or title)
        rationale = (
            f"Pin plan checklist ready_for_auto id={step.get('id')} "
            f"title={title!r}"
        )
        print(f"[saturday.pin_plans] checklist route rung={rung_id} action={action}")
        return action, target, rationale
    pin = next_live_auto_pin(plan)
    if pin is not None:
        decl = str(pin.get("lean_decl") or pin.get("id") or "")
        title = str(pin.get("title") or decl)
        target = f"formalize pin {decl}" if decl else f"formalize {title}"
        rationale = (
            f"Pin plan live ready_for_auto pin id={pin.get('id')} "
            f"decl={decl!r}"
        )
        print(f"[saturday.pin_plans] live pin route rung={rung_id} decl={decl!r}")
        return "formalize", target, rationale
    return None


# Default R2 seed used when no plan file exists yet (Block A closeout).
R2_SEED_PLAN: dict[str, Any] = {
    "checklist_ref": "docs/ladder/r2-block-a-factor2-checklist.md",
    "paused": False,
    "pause_reason": "",
    "ambient_red_streak": 0,
    "pins": [
        {
            "id": "spectral_hard_family",
            "title": "Spectral hard family (archival freeze)",
            "status": "archival",
            "lean_decl": "",
            "method_family": "spectral",
            "ready_for_auto": False,
            "notes": "Spectral route frozen; do not formalize as R2 close path.",
        },
        {
            "id": "cluster23_alpha1",
            "title": "Cluster 23 alpha=1 / density-6 CS",
            "status": "archival",
            "lean_decl": "exists_cs_clause_expanding_3cnf",
            "method_family": "cluster23",
            "ready_for_auto": False,
            "notes": "False at alpha=1; archived under cluster23_false_claim_archived.",
        },
        {
            "id": "cs_clause_expanding_restated",
            "title": "Restated CS pin (Tseitin Inv hardness)",
            "status": "done",
            "lean_decl": "exists_cs_clause_expanding_3cnf",
            "method_family": "tseitin_inv",
            "ready_for_auto": False,
            "notes": "Certified via cubic Inv / Tseitin Interchange (Block A item 7).",
        },
        {
            "id": "cubic_inv_tseitin",
            "title": "Cubic Inv / Tseitin hard family",
            "status": "done",
            "lean_decl": "",
            "method_family": "tseitin_inv",
            "ready_for_auto": False,
            "notes": "Block A item 6 closed (cubicInvK=164, floor 1968).",
        },
    ],
    "checklist": [
        {
            "id": "block_a_item_6",
            "title": "Cubic Inv / Tseitin hard family pin",
            "status": "done",
            "preferred_action": "formalize",
            "pin_id": "cubic_inv_tseitin",
            "notes": "Closed before pin-plans port.",
        },
        {
            "id": "block_a_item_7",
            "title": "CS clause-expanding pin (restated)",
            "status": "done",
            "preferred_action": "formalize",
            "pin_id": "cs_clause_expanding_restated",
            "notes": "Closed via Tseitin Inv hardness restatement.",
        },
        {
            "id": "r3_adopt_gate",
            "title": "Human adopt gate for R3 after R2 certify",
            "status": "ready_for_auto",
            "preferred_action": "audit",
            "pin_id": "",
            "notes": "Surface adopt decision; do not thrash formalize on R2.",
        },
    ],
    "notes": [
        {
            "at": "2026-09-25T00:00:00Z",
            "kind": "seed",
            "text": "Seeded from R2 Block A closeout (items 6-7 certified).",
        }
    ],
}
