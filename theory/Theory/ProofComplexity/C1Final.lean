import Theory.ProofComplexity.C1Tseitin
import Theory.ProofComplexity.C1Real

/-!
# Candidate C1: the bounded-rank lower bound (final theorem)

See `docs/ladder/rungs/r4-c1-lean-plan.md` for the honest reading: the statement is a corollary of
Pang's degree-size method (the layers are the formalized ones, re-run for the system `R_ρ^p`), the
constant `κ = (p-1) ln (cLam q)` is large, and the theorem is meaningful only for `(κ+1) ε < 1`.
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace C1

/-- **C1 (bounded rank).**  Let `p ∤ q` be primes (`q ≥ 2`), `ε > 0` with `(κ+1) ε < 1`, where
`κ = kappa p q = (p-1) ln (cLam q)`.  For every `M` there is a cubic graph on `n ≥ M` vertices such that
for every charge `b` and every rank bound `1 ≤ ρ ≤ ε ln n`, every dag-like `R_ρ^p` refutation of the one-hot
Tseitin mod `q` formula `tcnf G q b` (over its own variables) has at least `exp (n^(1-(κ+1) ε))` nodes. -/
theorem c1_main (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : RRefutation (tcnf G q b) (tVars G q) ρ p,
        Real.exp ((n : ℝ) ^ (1 - (kappa p q + 1) * ε)) ≤ R.S := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨M₀, hM₀⟩ := eventually_conditions p q hp ε hε
  obtain ⟨n, G, hN, hreg, H⟩ := c1_tseitin_exp' p hq hpq (max M M₀)
  have hnM₀ : M₀ ≤ n := (le_max_right _ _).trans hN
  obtain ⟨h2, hE1, hE2⟩ := hM₀ n hnM₀
  refine ⟨n, G, (le_max_left _ _).trans hN, hreg, fun b ρ hρ1 hρ R => ?_⟩
  obtain ⟨hc, hex⟩ := real_chain p q ρ n hp hq ε hε hεκ hρ1 hρ h2 hE1 hE2
  have hS := H b ρ hρ1 hc R
  refine hex.trans ?_
  exact_mod_cast hS

end C1
