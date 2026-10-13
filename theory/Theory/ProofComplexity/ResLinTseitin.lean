import Theory.ProofComplexity.ResLinFSize
import Theory.ProofComplexity.TseitinSize

/-!
# Width of Res(lin F_p) refutations of Tseitin mod q (Ladder Rung R4, Phase 2.2, layer 3a)

Combining Part-Tzameret Theorem 45 (`RLF.rld_cnf_pcd`: width `w` gives polynomial calculus degree
`w + 1`) with the certified polynomial calculus degree lower bound for the one hot Tseitin mod `q`
CNF over `ZMod p`, `p` prime not dividing `q` (`TseitinPC.tseitin_bool_degree_Fp`): every
tree-like `Res(lin F_p)` refutation of `tcnf G q b` on the cubic expander family has a line with
at least `D` equations, `D` linear in the number of vertices. The size bound (layer 3b, the
tree-like size-width relation, Part-Tzameret Theorem 44) is not yet formalized, so this is a
width bound only.

LOG: R4 Phase 2.2 ResLinTseitin module (width lower bound)
-/

namespace SATurday.ProofComplexity

open TseitinPC

theorem reslin_tseitin_width (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      q + 3 ≤ w →
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx) w ∅ s →
      ((n - 2) / 1312 - q * (q + 3)) / (q - 1) ≤ w + p := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ := tseitin_bool_degree_Fp p hq hpq N
  refine ⟨n, G, hN, hreg, fun b w s hw h => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  refine hdeg b (pcd_mono (by omega) (RLF.rld_cnf_pcd (fun a => ZMod.pow_card a) (by omega) (fun C hC => ?_) h))
  exact (tcnf_clause_props hreg hC).2.trans hw

/-- **Exponential tree-like size bound (one hot encoding)**: tree-like `Res(lin F_p)` refutations of
the one hot Tseitin mod `q` CNF on the cubic expanders have `2^{Ω(n)}` leaves. -/
theorem reslin_tseitin_size (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ := tseitin_bool_degree_Fp p hq hpq N
  refine ⟨n, G, hN, hreg, fun b w s h => ?_⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hs1 : 1 ≤ s := RLF.rld_pos h
  set D := ((n - 2) / 1312 - q * (q + 3)) / (q - 1) with hD
  set k := Nat.clog 2 s with hk
  have hlt : D < (q + 3) + (p - 1) * k + p := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hdeg b (pcd_mono hcon (RLF.rld_cnf_size (by omega) (fun C hC => ?_) h))
    exact (tcnf_clause_props hreg hC).2
  have h1 : (D - (q + 3) - p) / (p - 1) ≤ k := Nat.div_le_of_le_mul (by omega)
  refine le_trans (Nat.pow_le_pow_right (by norm_num) h1) ?_
  rcases Nat.lt_or_ge 1 s with hs | hs
  · have h2 : 2 ^ (k - 1) < s := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hs
    have hk1 : 1 ≤ k := Nat.clog_pos (by norm_num) hs
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have : s = 1 := by omega
    subst this
    simp [hk]

end SATurday.ProofComplexity
