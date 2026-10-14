import Theory.ProofComplexity.PangParams
import Theory.ProofComplexity.TseitinSize

/-!
# Pang route, layer I: exponential size for dag-like `Res(lin F_p)` refutations of Tseitin mod `q`

For primes `p ∤ q` there are cubic expanders `G` on `n ≥ N` vertices such that every dag-like
`Res(lin F_p)` refutation (in the sense of `Pang.Refutation`, lines over the variables of the CNF,
syntactic rules) of the one hot Tseitin mod `q` CNF `tcnf G q b`, for every charge `b`, has at least
`2^(n / C)` nodes, `C = Pang.cC p q`.
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace Pang

theorem card_G_le {n : ℕ} {G : FinGraph n} (hreg : IsRegular G 3) : G.card ≤ 3 * n := by
  classical
  have hsub : G ⊆ (Finset.univ : Finset (Fin n)).biUnion (incident G) := by
    intro e he
    exact Finset.mem_biUnion.2 ⟨e.val.1, Finset.mem_univ _, mem_incident_iff.2 ⟨he, Or.inl rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ v : Fin n, (incident G v).card = ∑ _v : Fin n, 3 := Finset.sum_congr rfl fun v _ => hreg v
    _ = 3 * n := by simp [mul_comm]

theorem card_tVars_le {n : ℕ} {q : ℕ} (G : FinGraph n) : (tVars G q).card ≤ G.card * q := by
  classical
  unfold tVars
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_product]

/-- **Exponential size for dag-like `Res(lin F_p)` on Tseitin mod `q`.** -/
theorem tseitin_dag_exp (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ R : Pang.Refutation (tcnf G q b) (tVars G q) p, 2 ^ (n / cC p q) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ := tseitin_bool_degree_Fp p hq hpq (max N (cN0 p q))
  have hn : cN0 p q ≤ n := (le_max_right _ _).trans hN
  have hn0 : 0 < n := by unfold cN0 at hn; omega
  refine ⟨n, G, (le_max_left _ _).trans hN, hreg, fun b R => ?_⟩
  refine exp_of_degree R hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 G
    omega
  · have h1 := card_tVars_le (q := q) G
    have h2 := card_G_le hreg
    calc (tVars G q).card ≤ G.card * q := h1
      _ ≤ (3 * n) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

end Pang
