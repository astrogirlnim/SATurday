import Theory.ProofComplexity.ResLinFPC
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

end SATurday.ProofComplexity
