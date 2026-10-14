import Theory.ProofComplexity.PangCube

/-!
# Pang route, layer G (part 2): the prefix identity `1 - P_L = ∑ U_i g_i`
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

lemma telescope (a : ℕ → PP p) (t : ℕ) :
    1 - ∏ j ∈ Finset.range t, a j = ∑ j ∈ Finset.range t, (∏ l ∈ Finset.range j, a l) * (1 - a j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ← ih]; ring

/-- `1 - ∏_j (1 - q_j^{p-1}) = ∑_i U_i g_i` with `deg U_i + d ≤ t (p-1) d`. -/
theorem prefix_identity {ι : Type*} (S : Finset ι) (g : ι → PP p) (c : ℕ → ι → ZMod p)
    {t d : ℕ} (ht : 1 ≤ t) (hg : ∀ i ∈ S, (g i).totalDegree ≤ d) :
    ∃ U : ι → PP p, (∀ i ∈ S, (U i).totalDegree + d ≤ t * ((p - 1) * d)) ∧
      1 - ∏ j ∈ Finset.range t, (1 - (∑ i ∈ S, c j i • g i) ^ (p - 1)) = ∑ i ∈ S, U i * g i := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set q : ℕ → PP p := fun j => ∑ i ∈ S, c j i • g i with hq
  have hqd : ∀ j, (q j).totalDegree ≤ d := fun j => by
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)
    exact (totalDegree_smul_le _ _).trans (hg i hi)
  set a : ℕ → PP p := fun j => 1 - q j ^ (p - 1) with ha
  have had : ∀ j, (a j).totalDegree ≤ (p - 1) * d := fun j => totalDegree_one_sub_pow_le (hqd j) _
  refine ⟨fun i => ∑ j ∈ Finset.range t, (∏ l ∈ Finset.range j, a l) * q j ^ (p - 2) * C (c j i), ?_, ?_⟩
  · intro i hi
    have hsum : (∑ j ∈ Finset.range t, (∏ l ∈ Finset.range j, a l) * q j ^ (p - 2) * C (c j i)).totalDegree
        + d ≤ t * ((p - 1) * d) := by
      have hne : (Finset.range t).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
      have hbound : (∑ j ∈ Finset.range t, (∏ l ∈ Finset.range j, a l) * q j ^ (p - 2) * C (c j i)).totalDegree
          ≤ t * ((p - 1) * d) - d := by
        refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)
        have hj' := Finset.mem_range.1 hj
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, add_zero]
        refine (totalDegree_mul _ _).trans ?_
        have e1 : (∏ l ∈ Finset.range j, a l).totalDegree ≤ j * ((p - 1) * d) := by
          refine (totalDegree_finset_prod _ _).trans ?_
          calc ∑ l ∈ Finset.range j, (a l).totalDegree ≤ ∑ _l ∈ Finset.range j, (p - 1) * d :=
                Finset.sum_le_sum fun l _ => had l
            _ = j * ((p - 1) * d) := by simp
        have e2 : (q j ^ (p - 2)).totalDegree ≤ (p - 2) * d :=
          (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hqd j))
        have e3 : (j + 1) * ((p - 1) * d) ≤ t * ((p - 1) * d) := Nat.mul_le_mul_right _ hj'
        have e4 : (p - 1) * d = (p - 2) * d + d := by
          rw [← Nat.succ_mul]; congr 1; omega
        have e5 : (j + 1) * ((p - 1) * d) = j * ((p - 1) * d) + ((p - 2) * d + d) := by
          rw [Nat.succ_mul, ← e4]
        omega
      have := hbound
      have h2 : d ≤ t * ((p - 1) * d) := by
        have : (p - 1) * d ≥ d := Nat.le_mul_of_pos_left d (by omega)
        nlinarith
      omega
    exact hsum
  · rw [telescope a t]
    have hqe : ∀ j, 1 - a j = q j ^ (p - 2) * q j := by
      intro j
      have : q j ^ (p - 1) = q j ^ (p - 2) * q j := by
        rw [← pow_succ]; congr 1; omega
      simp only [ha, sub_sub_cancel, this]
    have hqs : ∀ j, q j = ∑ i ∈ S, C (c j i) * g i := fun j => by
      simp only [hq, MvPolynomial.smul_eq_C_mul]
    have key : ∀ j, (∏ l ∈ Finset.range j, a l) * (1 - a j) =
        ∑ i ∈ S, ((∏ l ∈ Finset.range j, a l) * q j ^ (p - 2) * C (c j i)) * g i := by
      intro j
      calc (∏ l ∈ Finset.range j, a l) * (1 - a j)
          = ((∏ l ∈ Finset.range j, a l) * q j ^ (p - 2)) * q j := by rw [hqe j]; ring
        _ = ((∏ l ∈ Finset.range j, a l) * q j ^ (p - 2)) * ∑ i ∈ S, C (c j i) * g i := by
            congr 1; exact hqs j
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    simp only [key, Finset.sum_mul]
    exact Finset.sum_comm

end

end Pang
