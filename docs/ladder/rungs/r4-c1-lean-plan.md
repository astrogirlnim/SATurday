# R4 candidate C1: Lean plan and status (2026-10-14, branch r4/prover-c1lean)

Companion of r4-phase23-c1.md (statement, simulation by hand, parameter chain) and r4-pang-plan.md
section 10 (formalized Pang layers). Nothing here is certified.

## 1. Honest scope (first session; Section 3 below supersedes the conclusion that a degree-r Pang system is needed)

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

## 3. Status 2026-10-14 (second session): the final theorem IS reached

Key finding that changes Section 1: the degree-r generalization of the Pang system was NOT needed. The
Pang layers (`common_multiplier`, `onestep`, `prefix_identity`, `Nn_ratio`, `exp_bound`) are already stated
for an arbitrary degree bound d of the indicator polynomials g. Simulating R_rho^p directly with
g_T = polyOf (ml (chi T)) (degree <= d = (p-1) rho) works because the semantic rule is validated on the
cube (`cd_of_cube`), so no Fact BR / Fact U, no Res(PC_r) DAG, and no factor 3 from the translation.
The simulation steps of PangSim (`cover_step`, `claim_step`, `comb_step`, `mul_step`, init, Boolean axiom)
were re-stated for an arbitrary index type of equations (`C1Sim.lean`). Consequences, recorded honestly:

- Deviation from the c1 note: the exponent is d = (p-1) rho, not (p-1) * 3(p-1) rho, and the constants are
  those of the formalized layers (cA, cLam), not the paper's. So kappa_Lean = (p-1) ln (cLam q), cLam q =
  18 q (2624 q + 1313) (about 24.7 for (p,q) = (3,2); 12.4 for (2,3)), versus 140.9 in the note. The Lean
  statement is a different (cruder in constants, better in the 3(p-1) factor) instance of the same shape.
- `RRefutation` is over a fixed variable set V (no extension variables), exactly as `Pang.Refutation`.
- Quantifier shape: for every M there is n >= M (a graph from `tseitin_bool_degree_Fp`) such that the bound
  holds for all b and all 1 <= rho <= eps ln n. The bound is in the number n of vertices:
  exp(n^(1-(kappa+1) eps)), which implies the N-variable form of the note since N >= n.
- Hypothesis (kappa+1) eps < 1 is part of the statement (tiny eps only); for fixed rho the nat-form
  `c1_tseitin_exp` gives 2^(n / cCR p q ((p-1) rho)) with no analysis.
- Low novelty: a corollary of Pang's method, for the intermediate system R_rho^p.

Files (all in `theory/Theory/ProofComplexity/`):
`C1Rank` (system, soundness, chi), `C1Sim` (`c1_simulation_final`), `C1DegSize` (`c1_degree_size`,
`c1_size_exp`), `C1Params` (`exp_of_degree_R`, constants `cDminR`, `cN0R`, `cCR`), `C1Tseitin`
(`c1_tseitin_exp`, `c1_tseitin_exp'`), `C1Real` (`real_chain`, `eventually_conditions`, `kappa`), `C1Final`.

Final theorem `C1.c1_main` (axioms: propext, Classical.choice, Quot.sound):

```
theorem c1_main (p : N) [Fact p.Prime] {q : N} [NeZero q] (hq : 2 <= q) (hpq : not (p | q))
    (eps : R) (heps : 0 < eps) (hk : (kappa p q + 1) * eps < 1) (M : N) :
  exists n G, M <= n and IsRegular G 3 and forall b rho, 1 <= rho -> rho <= eps * Real.log n ->
    forall R : RRefutation (tcnf G q b) (tVars G q) rho p,
      Real.exp (n ^ (1 - (kappa p q + 1) * eps)) <= R.S
```
with `kappa p q = (p-1) * Real.log (cLam q)`.

## 4. Remaining / not done

- Matching the paper's sharper constant (ln S >= (D/(32 p^2 r)) (D/16 N)^((p-1) r)) is not attempted.
- The note's kappa is not reproduced; the Lean kappa is its own.
- Open mathematics (rank beyond log n, T1 of the c1 note) is untouched.
