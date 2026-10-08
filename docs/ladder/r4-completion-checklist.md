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

- [x] 1A.1 AC0[p] circuits as straight line programs (inputs, NOT, unbounded fan in AND,
  OR, MOD_{p,r}), semantics, depth and size.
- [x] 1A.2 Low degree functions over F_p on the Boolean cube (multilinear coefficient form),
  closed under sums and products with degree bounds.
- [x] 1A.3 Gate approximation: for OR (and AND by duality) some choice of `ℓ` random subsets
  gives a degree `(p - 1) ℓ` approximant wrong on at most a `2^{-ℓ}` fraction of inputs;
  MOD_{p,r} and NOT are exact.
- [x] 1A.4 Circuit approximation: a depth `d`, size `s` circuit agrees with a function of degree
  `((p - 1) ℓ)^d` on all but `s 2^{n - ℓ}` inputs (`circuit_approx`, Smolensky.lean).
- [x] 1A.5 Smolensky's argument for parity (p odd): on an agreement set `G` every function is
  of degree at most `n/2 + D`, so `|G| ≤ 2^{n-1} + (D + 1) C(n, ⌊n/2⌋)`; central binomial bound.
- [x] 1A.6 Theorem: for odd prime `p` and fixed depth `d`, AC0[p] circuits computing parity on
  `n` bits have super polynomial size (`smolensky_parity`, SmolenskyParity.lean, 2026-10-08).
- [ ] 1A.7 The case `p = 2` (MOD_3 or majority; needs F_4 roots of unity), deferred.

### 1B Bounded depth Frege: switching and PHP

- [x] 1B.1 Restrictions and decision trees; DNF width, consistent terms, canonical decision
  tree depth `cdtDepth` (Switching.lean).
- [x] 1B.2 Håstad's switching lemma (Razborov's encoding proof): restrictions with `ℓ` stars
  whose canonical tree has depth `≥ s` number at most `|R^{ℓ-s}| (4w)^s`
  (`switching_lemma`, 2026-10-08).
- [x] 1B.3 Matching restrictions and the PHP switching lemma: canonical matching trees
  (`mdepth`), coverage (`cover_of_mdepth`), Razborov style encoding (`mencode`), counting form
  `mswitching_ratio` (Matching.lean, MatchingSwitch.lean, 2026-10-08).
- [x] 1B.4 k evaluations for bounded depth Frege proofs: `Good`/`Local` conditions over a
  matching restriction, soundness of all 18 rules for mod free proofs (`step_sound`,
  `keval_sound`, `keval_no_refutation`), clauses of the R1 `phpCNF` are hit
  (`php_clauseHit`) (KEval.lean, PHPKEval.lean, 2026-10-08).
- [x] 1B.5 Theorem: bounded depth Frege refutations of PHP need super polynomial size
  (`php_bdfrege_superpoly`: for every `d`, `c`, all large `n`, every mod free depth `d`
  refutation of `phpCNF n` has `fSize > n^c`; KEvalBuild.lean, PHPFrege.lean, 2026-10-08).
  The exponential rate (`2^{n^{ε_d}}`) is not formalized; the super polynomial form matches
  the shape of `AC0pFregeLB`.

### 1C Algebraic systems over F_p

- [x] 1C.1 Polynomial calculus over a field: degree `d` derivations `PCD`, line degrees
  (`pcd_deg`), soundness (`pcd_sound`, `pc_cnf_unsat`) (PolyCalc.lean, 2026-10-08).
- [x] 1C.2 Degree lower bound for Tseitin mod q, binomial (Fourier) encoding: over any field with
  `ω^q = 1`, on a graph with inverse expansion `k` and max degree `≤ d`, `8kd + 2 ≤ n` rules out
  degree `d` PC refutations (`TseitinPC.tseitin_pc_degree`, Razborov R-operator); the system is
  unsatisfiable for primitive `ω` and nonzero total charge (`bt_no_root`); linear degree
  `(n - 2)/1312` on the certified cubic MGG expanders (`tseitin_pc_degree_cubic`)
  (TseitinPC.lean, 2026-10-08).
- [x] 1C.2b Transfer to the Boolean one hot encoding over F_p: substitution
  `x_{e,j} ↦ L_j(y_e)` (Lagrange indicators) into `CyclotomicField q F_p`, clause images
  derived via Alon's Combinatorial Nullstellensatz (`derive_grid`), simulation `simulate`;
  `tseitin_bool_degree_Fp`: for primes `p ∤ q`, on cubic expanders, no PC refutation over
  `ZMod p` of degree `((n-2)/1312 - q(q+3))/(q-1)`; unsatisfiability `tcnf_unsat`
  (TseitinBool.lean, 2026-10-08).
- [x] 1C.3 Size–degree tradeoff for polynomial calculus (multilinear proofs as line lists):
  `MLPC.ips` (Impagliazzo–Pudlák–Sgall induction), explicit form `MLPC.size_degree`,
  translation to PC `MLPC.translate`; consequence `TseitinPC.tseitin_ml_size`: over `ZMod p`
  (`p ∤ q`), multilinear PC refutations of one hot Tseitin mod q on cubic expanders have size
  `2^{Ω(n)}` (explicit exponent) (PCSizeDegree.lean, TseitinSize.lean, 2026-10-08).

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
