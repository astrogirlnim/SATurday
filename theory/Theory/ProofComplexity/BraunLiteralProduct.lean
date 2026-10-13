import Theory.ProofComplexity.BraunPC
import Mathlib.Tactic.Ring

/-!
# Products of affine literal complements (R4 Phase 2.1, layer 5a)

Credit. Port, with our own proof, of K. Braun (arXiv 2609.23015, author's Lean development):
`AffineLiteralProduct.lean` (`affine_literal_product_prefix`): an indexed product of complements
of degree at most one polynomials has explicit telescoping coefficients of degree at most
`n - 1`, including the empty family. Statement shape kept.

LOG: R4 BraunLiteralProduct module (Phase 2.1 layer 5a)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators

theorem affine_literal_product_prefix {K σ : Type} [Field K] (n : ℕ) (g : Fin n → Poly K σ)
    (hg : ∀ i, (g i).totalDegree ≤ 1) :
    ∃ U : Fin n → Poly K σ,
      1 - ∏ i, (1 - g i) = ∑ i, U i * g i ∧ ∀ i, (U i).totalDegree ≤ n - 1 := by
  induction n with
  | zero => exact ⟨Fin.elim0, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨U, hU, hdeg⟩ := ih (fun i => g i.succ) (fun i => hg i.succ)
    let V : Fin (n + 1) → Poly K σ := Fin.cases 1 (fun i => (1 - g 0) * U i)
    refine ⟨V, ?_, ?_⟩
    · rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      simp only [V, Fin.cases_zero, Fin.cases_succ, one_mul]
      have hs : (∑ i : Fin n, (1 - g 0) * U i * g i.succ) =
          (1 - g 0) * ∑ i : Fin n, U i * g i.succ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs, ← hU]
      ring
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [V]
      · have hj := j.isLt
        have h0 := hg 0
        have hd := hdeg j
        change ((1 - g 0) * U j).totalDegree ≤ (n + 1) - 1
        apply (totalDegree_mul _ _).trans
        have hf := totalDegree_sub (1 : Poly K σ) (g 0)
        simp only [totalDegree_one, Nat.zero_max] at hf
        omega

end

end SATurday.ProofComplexity.BraunPC
