# R3: One Certified Bound Above Resolution

Status: active
Lean home: theory/Theory/ProofComplexity/CuttingPlanes.lean

## Statement

One certified super-polynomial lower bound for a system strictly stronger than
resolution. Candidates, to be selected by prover cycles on formalization cost and
technique reuse toward R4:

1. Res(k) (resolution over k-DNFs) lower bounds.
2. Cutting planes lower bounds via feasible interpolation (Pudlak 1997) for
   clique-coloring formulas.
3. Bounded-depth Frege lower bounds for PHP (Ajtai; Pitassi-Beame-Impagliazzo;
   Krajicek-Pudlak-Woods).

## Why this rung

First step above resolution. Each candidate exercises a technique class
(k-DNF switching, interpolation, restriction-based depth reduction) whose reach and
walls must be understood before R4 work is credible.

## Falsification test

Per candidate family: empirical proof-size calibration where a solver-checkable
fragment exists; literature check for upper bounds killing the family.

## Barrier notes

Interpolation is known to die above this level (Bonet-Pitassi-Raz for TC0-Frege
under factoring hardness; Krajicek-Pudlak for extended Frege under RSA); an
interpolation-based R3 result must be documented as non-extendable, acceptable for
R3 but not as the R4 plan.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed.
- 2026-10-07 adopt (human gate, operator request): candidate 2, cutting planes via
  monotone feasible interpolation for clique coloring. Rationale: the argument splits
  into two self contained obligations (Pudlák interpolation, monotone real circuit
  bound) joined by a short certified packaging step, and cutting planes is strictly
  stronger than resolution. Barrier note recorded: interpolation does not extend to
  R4, so R4 needs a different technique.
  Lean surface certified the same day in `CuttingPlanes.lean`: dag CP proofs and
  soundness (`cpRefutes_unsat`), clique coloring split into `cliqueCNF` and
  `colorCNF` with non vacuity `ccCNF_unsat` (m < k), monotone real circuits as
  straight line programs, and `cp_superpoly_of_interp_lb`. Open pins:
  `CuttingPlanesFrontier.cp_monotone_interpolation`,
  `CuttingPlanesFrontier.monoReal_clique_lb`. Plan:
  docs/ladder/r3-cutting-planes-checklist.md.

- 2026-10-07 local saturday formalize: result=blocked; artifacts: search/logs/saturday_drafts/20261007T223959Z_r3-stronger-systems_formalize_local.lean, theory/Theory/ProofComplexity/CuttingPlanes.lean; learned: This is a placeholder for the actual proof of cp_monotone_interpolation. The proof will be added in a future update. | accepted_select=60/2201 draft_gate reject: sorry_replace discharge forbids sorry in the draft body; use status=blocked with empty lean if the pin is not closable; blocked_method

namespace CuttingPlanesFrontier

theorem cp_monotone_interpolation : CPMonotoneInterpolation := by
  sorry

end CuttingPlanesFrontier

- 2026-10-07 local saturday formalize: result=blocked; artifacts: search/logs/saturday_drafts/20261007T224053Z_r3-stronger-systems_formalize_local.lean, theory/Theory/ProofComplexity/CuttingPlanes.lean; learned: This is a placeholder for the actual proof of cp_monotone_interpolation. The proof will be added in a future update. | accepted_select=60/2201 draft_gate reject: model marked status=blocked; refusing apply (missing Lean surface); blocked_method

namespace CuttingPlanesFrontier

theorem cp_monotone_interpolation : CPMonotoneInterpolation := by
  sorry

end CuttingPlanesFrontier
- 2026-10-07 formalize (operator session, loop paused): the local loop's own micro
  split restated certified lemmas and the whole theorem, so the session wrote Pudlák's
  construction directly. Certified `cp_monotone_interpolation_proof : CPMonotoneInterpolation`
  in `CuttingPlanesInterp.lean`: per line bounds `DD` with invariants `DD_inv` (A side,
  B side, sum), and a monotone real circuit `interpCircuit` computing `- DA` line by line
  (`val_posN`), size `|P| + lines (|P| + 1) + 1`. `cp_superpoly_of_lb` reduces the R3
  target to the single open pin `CuttingPlanesFrontier.monoReal_clique_lb`. Axioms
  standard. Lesson: local 14B models cannot design a construction; they need precise
  micro statements.
