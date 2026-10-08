# R4 Completion Checklist

Source: `docs/ladder/r4-research-plan.md`. Work in order; check items off only when the
axiom gate passes (`bash scripts/check_axioms.sh`) for certified items, or when the stated
document change is committed for process items.

Acceptance bar: `lake build` green, zero sorry outside Frontier namespaces, axioms within
propext, Classical.choice, Quot.sound; new declarations listed in
`scripts/accepted_declarations.txt`; CI axiom gate green.

## Phase 0: adopt and lock the target

- [x] 0.1 Adopt R4 (operator "go", 2026-10-08): rung status active, ladder updated, loop
  wiring (workstream R4, Lean target `AC0pFrege.lean`, Frontier namespace
  `AC0pFregeFrontier`, pin plan seed `R4_SEED_PLAN`).
- [x] 0.2 Lean definitions of the target system: formulas `Fm` with AND, OR, NOT and MOD_p
  connectives, `Fm.depth`, `Fm.size`, `Fm.eval`.
- [x] 0.3 Lean definition of the proof system: dag like sequent calculus with MOD_p defining
  axioms (`FStep`, `FProof`, `FRefutes p d F L`, `fSize`), soundness `frefutes_unsat`.
- [x] 0.4 Locked R4 statement as the Frontier pin `AC0pFregeFrontier.r4_target`:
  for every prime `p`, `AC0pFregeLB p` (a polynomial size family of unsatisfiable CNFs whose
  depth `d` refutations need super polynomial size, for every `d`). Candidate families
  recorded in the rung memory (Tseitin mod q on expanders, Count_q, onto PHP, random k CNF).
- [x] 0.5 Non vacuity witness: every unsatisfiable CNF has a depth one AC0[p] Frege
  refutation (`frefutes_of_unsat`, by simulating resolution), so the bounds are about proof
  size and not about provability.
- [x] 0.6 Kill conditions recorded in the rung memory (T4.1 upper bound, T4.2 barrier,
  three failed attempts per method).

## Phase 1: certified infrastructure (known mathematics)

### 1A Circuit analogue: Razborov–Smolensky (Smolensky's form, odd p, parity)

- [ ] 1A.1 AC0[p] circuits as straight line programs (inputs, NOT, unbounded fan in AND,
  OR, MOD_{p,r}), semantics, depth and size.
- [ ] 1A.2 Low degree functions over F_p on the Boolean cube (multilinear coefficient form),
  closed under sums and products with degree bounds.
- [ ] 1A.3 Gate approximation: for OR (and AND by duality) some choice of `ℓ` random subsets
  gives a degree `(p - 1) ℓ` approximant wrong on at most a `2^{-ℓ}` fraction of inputs;
  MOD_{p,r} and NOT are exact.
- [ ] 1A.4 Circuit approximation: a depth `d`, size `s` circuit agrees with a function of degree
  `((p - 1) ℓ)^d` on all but `s 2^{n - ℓ}` inputs.
- [ ] 1A.5 Smolensky's argument for parity (p odd): on an agreement set `G` every function is
  of degree at most `n/2 + D`, so `|G| ≤ 2^{n-1} + (D + 1) C(n, ⌊n/2⌋)`; central binomial bound.
- [ ] 1A.6 Theorem: for odd prime `p` and fixed depth `d`, AC0[p] circuits computing parity on
  `n` bits have super polynomial size.
- [ ] 1A.7 The case `p = 2` (MOD_3 or majority; needs F_4 roots of unity), deferred.

### 1B Bounded depth Frege: switching and PHP

- [ ] 1B.1 Restrictions and decision trees; DNF and CNF width.
- [ ] 1B.2 Håstad's switching lemma (Razborov's encoding proof).
- [ ] 1B.3 Matching restrictions and the PHP switching lemma.
- [ ] 1B.4 k evaluations for bounded depth Frege proofs.
- [ ] 1B.5 Theorem: bounded depth Frege refutations of PHP need exponential size.

### 1C Algebraic systems over F_p

- [ ] 1C.1 Polynomial calculus over F_p: definitions, soundness, degree.
- [ ] 1C.2 Degree lower bound for Tseitin mod q over F_p (q ≠ p).
- [ ] 1C.3 Size–degree tradeoff for polynomial calculus.

### 1D Known partial results toward AC0[p] Frege

- [ ] 1D.1 Literature pass with citations recorded in the rung memory.
- [ ] 1D.2 Count_q lower bound for bounded depth Frege with Count_p axioms.
- [ ] 1D.3 Res(⊕) lower bounds known so far (regular or bounded depth variants).

## Phase 2: intermediate open targets (research)

- [ ] 2.1 Res(⊕) in full generality: prose attempt, barrier audit, counterexample attempts.
- [ ] 2.2 Res(lin F_p).
- [ ] 2.3 Depth 2 AC0[p] Frege.
- [ ] 2.4 Constant depth AC0[p] Frege (this is R4 itself).
- Stop rule: 3 failed attempts on one method kill that method branch.

## Phase 3: certify R4

- [ ] 3.1 Prose proof survives barrier audit and red team.
- [ ] 3.2 Formalization of the Phase 0 pin, axiom gate PASS, CI green.
- [ ] 3.3 Independent expert review of statement fidelity.
- [ ] 3.4 Human gate: R4 certified.
