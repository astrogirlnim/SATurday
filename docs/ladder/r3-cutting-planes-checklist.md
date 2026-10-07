# R3 Completion Checklist: Cutting Planes via Monotone Interpolation

Adopted 2026-10-07 (human gate). Lean home:
`theory/Theory/ProofComplexity/CuttingPlanes.lean`, Frontier namespace
`CuttingPlanesFrontier`. Pin plan: `search/logs/pin_plans/r3-stronger-systems.json`
(seeded from `R3_SEED_PLAN` in `search/saturday/pin_plans.py`).

Acceptance bar: `lake build` green, zero sorry outside Frontier, axioms within
propext, Classical.choice, Quot.sound (`bash scripts/check_axioms.sh`).

## Target

`CPCliqueColoringSuperpoly`: for every `c` there is `N` such that for `n ≥ N`
every CP refutation of `ccCNF n k (k - 1)`, `k = ⌊n^{1/4}⌋`, has more than `n^c`
lines.

Barrier note: interpolation does not extend above this level (Bonet Pitassi Raz;
Krajíček Pudlák). This closes R3 only; it is not the R4 plan.

## Certified surface (2026-10-07)

- [x] CP lines, dag proofs as line lists (sum, positive scaling, division with
  rounding), soundness `cpRefutes_unsat`.
- [x] Clique coloring split `ccCNF = cliqueCNF ∪ colorCNF` with edge, clique and
  color variables in disjoint ranges; non vacuity `ccCNF_unsat` for `m < k`.
- [x] Monotone real circuits as straight line programs (`MGate`, `mcEval`, size is
  the number of gates).
- [x] Packaging `cp_superpoly_of_interp_lb : CPMonotoneInterpolation →
  MonoRealCliqueLB → CPCliqueColoringSuperpoly` (variable side conditions,
  disjointness, variable count, polynomial arithmetic).

## Obligation 1: `cp_monotone_interpolation` (Pudlák 1997)

Micro plan, in order. Fix the `p` part of an assignment throughout.

- [ ] I1. Split a line into its `P`, `Q` and `R` coefficient parts.
- [ ] I2. For a fixed `p`, define along the proof a pair of integer bounds
  `(DA, DB)` per line: hypothesis clauses from `A` put everything on the A side,
  clauses from `B` on the B side, axioms on the side of their variable; sum and
  scaling act componentwise; division rounds each side (the `P` coefficients go
  to the A side so divisibility holds on each half).
- [ ] I3. A side soundness: any `(p, q)` satisfying `A` satisfies
  `Q part ≥ DA` for every line.
- [ ] I4. B side soundness: any `(p, r)` satisfying `B` satisfies
  `R part ≥ DB` for every line.
- [ ] I5. Invariant `DA + DB ≥ rhs - (P part at p)` and, on the final line
  `0 ≥ b` with `b > 0`, `DA + DB ≥ 1`.
- [ ] I6. Monotonicity: `- DA` is nondecreasing in `p` (since `p` occurs only
  positively in `A`), computed by a block of monotone real gates per line
  (addition, positive scaling, ceiling of a division); output gate
  `[ -DA ≥ 0 ]`. Size at most a constant times (lines + variables).
- [ ] I7. Assemble `CPMonotoneInterpolation` with an explicit polynomial.

## Obligation 2: `monoReal_clique_lb`

Approximation method for monotone real gates (Pudlák 1997; Haken and Cook 1999;
Alon and Boppana bound `2^{Ω(√k)}`).

- [ ] L1. Test graphs: positive tests are single `k` cliques; negative tests are
  complete `(k - 1)` partite graphs from colorings `[n] → [k - 1]`.
- [ ] L2. Positive tests satisfy `cliqueCNF n k`; negative tests satisfy
  `colorCNF n k (k - 1)` (with witnesses for the clique and color variables), so a
  separating circuit is `1` on positive and `0` on negative tests.
- [ ] L3. Real gate reduction: thresholds of a monotone real circuit give
  monotone Boolean functions per gate; approximate each by a clique indicator
  union.
- [ ] L4. Sunflower lemma (Erdős Rado) in the needed form.
- [ ] L5. Error bounds per gate on positive and negative tests.
- [ ] L6. Size `≥ 2^{Ω(√k)}`, then super polynomial in `n` for `k = ⌊n^{1/4}⌋`.

## Close

- [ ] Both pins discharged; `cp_cliqueColoring_superpoly` sorry free.
- [ ] Add decls to `scripts/accepted_declarations.txt`; axiom gate PASS.
- [ ] Human gate: R3 `certified`; document technique and walls toward R4.
