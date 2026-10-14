# R4 candidate C1: Lean plan and status (2026-10-14, branch r4/prover-c1lean)

Companion of r4-phase23-c1.md (statement, simulation by hand, parameter chain) and r4-pang-plan.md
section 10 (formalized Pang layers). Nothing here is certified.

## 1. Honest scope

- C1 is a corollary of Pang's degree-size theorem for Res(PC_r/F_p) with r = 3(p-1)rho. Low novelty:
  the only new object is the system R_rho^p. The constant kappa is huge (140.9 for (p,q) = (3,2)), so the
  bound is meaningful only for tiny epsilon and astronomically large N.
- What is formalized of Pang is the case r = 1 ONLY: `Pang.Refutation` (file PangDag) has lines that are
  finite sets of equations of degree <= 1 in the CNF's variables (rules: init, 0=0, Boolean axiom, weakening,
  false-constant deletion, linear combination, multiplication with the product of degree <= 1; no extension
  variables, no cut). `Pang.simulation_final` is Proposition 5.1 for r = 1 and `Pang.tseitin_dag_exp` gives
  2^(n / cC p q) <= R.S with a constant that does not depend on r (it was derived for r = 1: K = D/4, t = D/(8(p-1)^2)).
- Consequence: C1 cannot be deduced from the existing theorem. Not even rho = 1 works: the semantic rule Sem on
  rank-1 terms needs the unit-equation Fact U and a product of three indicators, degree 3(p-1) >= 3 > 1. Only the
  purely syntactic subsystem (rank-1 terms, linear combination, multiplication) is Res(lin F_p), which is
  Pang's own system, so restating it would add nothing.

## 2. Exact target statement (Lean form, NOT proved)

```
theorem c1 (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) (ε : ℝ) (hε : 0 < ε) :
  ∃ κ : ℝ, ∃ M₀ : ℕ, ∀ m ≥ M₀, ∃ G : FinGraph m, IsRegular G 3 ∧ ∀ b : Fin m → ZMod q,
    (∑ v, b v ≠ 0) → ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log m →
    ∀ R : C1.RRefutation (tcnf G q b) ρ p,
      Real.exp ((N : ℝ) ^ (1 - (κ + 1) * ε)) ≤ R.S        -- N = |tVars G q|
```
with kappa = 3(p-1)^2 ln(62976 q (q-1)). The definitions (`C1.RRefutation`, size = S = number of nodes, lines
= finite sets of terms, term = finite set of affine forms over F_p with rank = dim of the span, constants
included) are in `C1Rank.lean`. Unsatisfiability of the one-hot Tseitin target is already `tcnf` +
`tseitin_bool_degree_Fp` (the formula has no refutation when sum b = 0 because it is then satisfiable; the
hypothesis sum b != 0 is not even needed for the lower bound statement, since a refutation implies unsat by
`RRefutation.unsat`).

## 3. Done in this session (merged, `C1Rank.lean`, axioms propext/Classical.choice/Quot.sound)

- `AffForm`, `ev` (linear in the form), `formPoly`, `Term`, `rank`, `RLine`, `Bdd`, `LTrue`.
- `RInfer` (init, taut, weak, sem1, sem2 with `SemOK` = semantic consequence on the Boolean cube, T3 optional),
  `RRefutation` with size S, `RInfer.sound`, `RRefutation.unsat`.
- Translation `chi T = prod_{l in B_T} (1 - l^(p-1))`, `B_T` a chosen maximal independent subset
  (`basisOf`, `card_basisOf` : |B_T| = rank T): `eval_chi` (0/1 indicator of the term at EVERY point of F_p^N,
  hence on the cube), `totalDegree_chi` (<= (p-1) rank T), `LTrue_iff_chi` (soundness of the translation of a line
  into the clause of equations chi_T - 1 = 0).

## 4. Not done, and cost

1. Degree r Pang system and simulation lemma (Lemma 1 of the c1 note): a `PangDag` generalized from degree 1
   to degree r (mechanical, ~130 lines, soundness copies), Fact BR (Boolean reduction by division, ~150 lines)
   and Fact U (unit equation, ~100 lines), the sem1/sem2 cases (~250 lines). Estimated 500-700 lines.
2. The degree r lower bound: `PangSim` (497), `PangPrefix` (90) and the parameter files (`PangDegSize`,
   `PangExp`, `PangSizeExp`, `PangParams`, ~350) must be redone with polynomial lines of degree r, i.e. the
   multiplication/cover/claim steps with indicators of degree-r polynomials, `prefix_identity` with the shift d,
   and the new factor (D/16N)^((p-1)r). The abstract layers (`PangMult`..`PangCommon`, `onestep` with parameter d)
   look reusable. Estimate 1200-1800 lines, 2-3 sessions, and the main risk is in `PangSim`.
3. The numeric chain (kappa, the choice D = D_0, the estimate for ln S in terms of N^(1-(kappa+1)eps)) in real
   arithmetic, ~300 lines of inequalities. It cannot be done before item 2 because the existing bound has
   the shape 2^(n/C) with an r-independent C.

Total: a multi-session job. The honest stopping point of this session is the merged `C1Rank.lean`.
