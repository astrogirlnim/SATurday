import Theory.ProofComplexity.C1Params
import Theory.ProofComplexity.PangTseitin

/-!
# Candidate C1: exponential size for `R_ρ^p` refutations of Tseitin mod `q` (natural number form)
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace C1

/-- **Exponential size for `R_ρ^p` on one-hot Tseitin mod `q`**, for a fixed rank bound `ρ ≥ 1`
(`d = (p-1) ρ`): there are cubic graphs on `n ≥ N` vertices such that for every charge `b` every
`R_ρ^p` refutation (over the variables of the formula) has at least `2^(n / cCR p q d)` nodes. -/
theorem c1_tseitin_exp (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ρ : ℕ) (hρ : 1 ≤ ρ) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ R : RRefutation (tcnf G q b) (tVars G q) ρ p,
        2 ^ (n / cCR p q ((p - 1) * ρ)) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ :=
    tseitin_bool_degree_Fp p hq hpq (max N (cN0R p q ((p - 1) * ρ)))
  have hn : cN0R p q ((p - 1) * ρ) ≤ n := (le_max_right _ _).trans hN
  have hn0 : 0 < n := by unfold cN0R at hn; omega
  refine ⟨n, G, (le_max_left _ _).trans hN, hreg, fun b R => ?_⟩
  refine exp_of_degree_R R rfl hρ hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 G
    omega
  · have h1 := Pang.card_tVars_le (q := q) G
    have h2 := Pang.card_G_le hreg
    calc (tVars G q).card ≤ G.card * q := h1
      _ ≤ (3 * n) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

/-- Variant of `c1_tseitin_exp` in which the size threshold `cN0R p q ((p-1) ρ) ≤ n` is a hypothesis
checked after the graph is chosen, so one graph serves all admissible `ρ` at once. -/
theorem c1_tseitin_exp' (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → cN0R p q ((p - 1) * ρ) ≤ n →
      ∀ R : RRefutation (tcnf G q b) (tVars G q) ρ p,
        2 ^ (n / cCR p q ((p - 1) * ρ)) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ := tseitin_bool_degree_Fp p hq hpq N
  refine ⟨n, G, hN, hreg, fun b ρ hρ hn R => ?_⟩
  have hn0 : 0 < n := by unfold cN0R at hn; omega
  refine exp_of_degree_R R rfl hρ hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 G
    omega
  · have h1 := Pang.card_tVars_le (q := q) G
    have h2 := Pang.card_G_le hreg
    calc (tVars G q).card ≤ G.card * q := h1
      _ ≤ (3 * n) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

end C1
