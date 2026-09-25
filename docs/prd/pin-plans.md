# PRD: Pin Plans and Chooser Contract

Status: accepted (2026-09-25)  
Owner: saturday loop (`satday auto`)  
Audience: implementers of `search/saturday/` and operators running Block B+

## 1. Summary

Give the loop a **pin health and checklist control plane** so it stops
formalizing dead equations, respects per-rung pauses without a global kill,
and targets the next `ready_for_auto` checklist step instead of grinding the
nearest Frontier `sorry`.

This addresses the R2 Block A failure mode: 100+ formalize wakes on false
spectral or Cluster 23 pins while the real close was a human checklist and a
pin restatement.

## 2. Problem

- Chooser treated every open Frontier `sorry` as a formalize target.
- Global `saturday_KILL` froze R2 and R5 together.
- Ambient lake red produced dozens of identical blocked wakes.
- Plateau recovery stayed on `formalize`, amplifying thrash.
- Import decompose micros could not redesign a dead pin statement.
- The factor-2 checklist that closed Block A lived outside the chooser.

## 3. Goals

1. Persist per-rung **pin plans** (`search/logs/pin_plans/<rung>.json`).
2. Pin statuses: `live`, `dead`, `restated`, `archival`, `done`,
   `blocked_missing_surface`.
3. Chooser refuses `formalize` on `dead` / `archival` / missing-surface pins.
4. Prefer the next checklist step with `ready_for_auto` as the cycle target.
5. Per-rung pause without engaging global kill (`auto_kill_scope: rung`).
6. Ambient lake red skips formalize model spend and does not count as pin
   progress; escalate to audit / pause after a streak.
7. Draft gate rejects placeholder or `sorry` discharges for live pins.
8. Plateau default recovery switches to `prove` (method audit / restatement).

## 4. Non goals

- Automatic restatement of Lean Frontier equations without a prove cycle.
- Replacing human `merge_certified` / adopt gates.
- Translating Isabelle proofs into Lean axioms.

## 5. Artifacts

| Path | Role |
| --- | --- |
| `search/logs/pin_plans/<rung_id>.json` | Runtime pin and checklist state |
| `search/saturday/pin_plans.py` | Load / save / query / mutate |
| `docs/ladder/*-checklist.md` | Human readable checklist (optional ref) |

## 6. Chooser contract

Order of preference for a rung action:

1. Operator / reflect `force_action` (sticky operator wins).
2. Pending decompose micro (only if parent pin is `live` or `ready_for_auto`).
3. Next checklist step with `status=ready_for_auto`.
4. Next pin with `status=live` and `ready_for_auto`.
5. Import ladder step when surface exists.
6. Default prove / formalize / falsify / audit rules.

Hard refuses:

- `formalize` on pin status in `{dead, archival, blocked_missing_surface}`.
- Formalize when ambient lake is red (`formalize_require_green_lake`).
- Applying drafts that still contain `sorry` or `status=blocked` with Lean.

## 7. Kill vs pause

- `auto_kill_scope: rung` (default): plateau pauses that rung only.
- Global kill remains for operator `satday kill` and true cross-rung stop.
- Loop stops when every actionable rung is paused or certified, without
  requiring a global kill flag.

## 8. Acceptance

- Unit behavior covered by CLI dry inspection (`satday pin status`).
- R2 seed plan marks Cluster 23 archival and Tseitin Inv route done.
- `plateau_switch_action` default is `prove`.
- Clearing obsolete spectral global freeze is an operator action after port.

## 9. References

- `docs/prd/proof-import.md` (import micros; surface gate)
- `docs/ladder/r2-block-a-factor2-checklist.md` (worked example)
- `search/saturday/chooser.py`, `reflect.py`, `control.py`, `draft_gate.py`
