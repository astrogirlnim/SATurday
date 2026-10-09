import Mathlib

/-!
# Rado's theorem for linear independence (Welsh 1971)

If `V_i` (`i ∈ ι`, `ι` finite) are finite sets of vectors in a finite dimensional vector space and
every subfamily `A` satisfies `|A| ≤ dim span (⋃_{i∈A} V_i)`, then one can pick `v_i ∈ V_i` with
`(v_i)` linearly independent. This is the vector space form of Hall's theorem used by
Efremenko–Garlik–Itsykson (ECCC TR23-187, Theorem 3.2) for safe sets of linear forms.

Proof (Rado's critical sets): reduce the total size by deleting a vector from some `V_i` with at
least two vectors; if two different deletions both fail, the submodular inequality
`dim (X + Y) + dim (X ∩ Y) = dim X + dim Y` gives a contradiction.

LOG: R4 Rado module (matroid Hall theorem for vector spaces)
-/

namespace SATurday.ProofComplexity

namespace Rado

open Module Finset

variable {K L ι : Type*} [Field K] [AddCommGroup L] [Module K L] [DecidableEq ι] [DecidableEq L]

/-- The span of the union of the sets indexed by `A`. -/
def spanU (K : Type*) [Field K] {L ι : Type*} [AddCommGroup L] [Module K L]
    (V : ι → Finset L) (A : Finset ι) : Submodule K L :=
  Submodule.span K (⋃ i ∈ A, (V i : Set L))

/-- Rado's condition. -/
def Cond (K : Type*) [Field K] {L ι : Type*} [AddCommGroup L] [Module K L]
    (V : ι → Finset L) : Prop := ∀ A : Finset ι, A.card ≤ finrank K (spanU K V A)

theorem spanU_mono (V : ι → Finset L) {A B : Finset ι} (h : A ⊆ B) :
    spanU K V A ≤ spanU K V B :=
  Submodule.span_mono (Set.iUnion₂_mono' fun i hi => ⟨i, h hi, subset_rfl⟩)

theorem spanU_congr (V V' : ι → Finset L) {A : Finset ι} (h : ∀ i ∈ A, V i = V' i) :
    spanU K V A = spanU K V' A := by
  unfold spanU
  congr 1
  exact Set.iUnion₂_congr fun i hi => by rw [h i hi]

/-- Deleting one vector from a set with two vectors while keeping Rado's condition. -/
theorem exists_delete [FiniteDimensional K L] {V : ι → Finset L} (hV : Cond K V) {i0 : ι}
    (h2 : 2 ≤ (V i0).card) :
    ∃ u ∈ V i0, Cond K (Function.update V i0 ((V i0).erase u)) := by
  by_contra hcon
  push Not at hcon
  -- any failing family must contain `i0`
  have hfail : ∀ u ∈ V i0, ∃ A : Finset ι, i0 ∈ A ∧
      finrank K (spanU K (Function.update V i0 ((V i0).erase u)) A) < A.card := by
    intro u hu
    have hc := hcon u hu
    unfold Cond at hc
    push Not at hc
    obtain ⟨A, hA⟩ := hc
    refine ⟨A, ?_, hA⟩
    by_contra hnot
    have heq : spanU K (Function.update V i0 ((V i0).erase u)) A = spanU K V A :=
      (spanU_congr V _ (fun i hi => (Function.update_of_ne (fun h : i = i0 => hnot (by rw [← h]; exact hi)) _ _).symm)).symm
    have := hV A
    rw [heq] at hA
    omega
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.1 (by omega : 1 < (V i0).card)
  obtain ⟨A, hA0, hA⟩ := hfail u hu
  obtain ⟨B, hB0, hB⟩ := hfail w hw
  set Vu := Function.update V i0 ((V i0).erase u) with hVu
  set Vw := Function.update V i0 ((V i0).erase w) with hVw
  set X := spanU K Vu A
  set Y := spanU K Vw B
  -- X + Y contains all of V on A ∪ B
  have hsup : spanU K V (A ∪ B) ≤ X ⊔ Y := by
    apply Submodule.span_le.2
    intro z hz
    simp only [Set.mem_iUnion, mem_coe] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    rcases mem_union.1 hi with hiA | hiB
    · by_cases hi0 : i = i0
      · subst hi0
        by_cases hzu : z = u
        · have : z ∈ (Vw i) := by simp [hVw, mem_erase, hzu, huw]; exact hu
          exact Submodule.mem_sup_right (Submodule.subset_span (by
            simp only [Set.mem_iUnion, mem_coe]; exact ⟨i, hB0, this⟩))
        · have : z ∈ (Vu i) := by simp [hVu, mem_erase, hzu]; exact hzi
          exact Submodule.mem_sup_left (Submodule.subset_span (by
            simp only [Set.mem_iUnion, mem_coe]; exact ⟨i, hiA, this⟩))
      · have : z ∈ (Vu i) := by simp [hVu, Function.update_of_ne hi0]; exact hzi
        exact Submodule.mem_sup_left (Submodule.subset_span (by
          simp only [Set.mem_iUnion, mem_coe]; exact ⟨i, hiA, this⟩))
    · by_cases hi0 : i = i0
      · subst hi0
        by_cases hzw : z = w
        · have : z ∈ (Vu i) := by simp [hVu, mem_erase, hzw, Ne.symm huw]; exact hw
          exact Submodule.mem_sup_left (Submodule.subset_span (by
            simp only [Set.mem_iUnion, mem_coe]; exact ⟨i, hA0, this⟩))
        · have : z ∈ (Vw i) := by simp [hVw, mem_erase, hzw]; exact hzi
          exact Submodule.mem_sup_right (Submodule.subset_span (by
            simp only [Set.mem_iUnion, mem_coe]; exact ⟨i, hiB, this⟩))
      · have : z ∈ (Vw i) := by simp [hVw, Function.update_of_ne hi0]; exact hzi
        exact Submodule.mem_sup_right (Submodule.subset_span (by
          simp only [Set.mem_iUnion, mem_coe]; exact ⟨i, hiB, this⟩))
  -- X ∩ Y contains V on (A ∩ B) \ {i0}
  have hinf : spanU K V ((A ∩ B).erase i0) ≤ X ⊓ Y := by
    apply le_inf
    · have e : spanU K V ((A ∩ B).erase i0) = spanU K Vu ((A ∩ B).erase i0) :=
        spanU_congr V Vu (fun i hi => (Function.update_of_ne (mem_erase.1 hi).1 _ _).symm)
      show spanU K V _ ≤ spanU K Vu A
      rw [e]
      exact spanU_mono Vu (fun i hi => (mem_inter.1 (mem_erase.1 hi).2).1)
    · have e : spanU K V ((A ∩ B).erase i0) = spanU K Vw ((A ∩ B).erase i0) :=
        spanU_congr V Vw (fun i hi => (Function.update_of_ne (mem_erase.1 hi).1 _ _).symm)
      show spanU K V _ ≤ spanU K Vw B
      rw [e]
      exact spanU_mono Vw (fun i hi => (mem_inter.1 (mem_erase.1 hi).2).2)
  have e := Submodule.finrank_sup_add_finrank_inf_eq X Y
  have m1 := Submodule.finrank_mono hsup
  have m2 := Submodule.finrank_mono hinf
  have c1 := hV (A ∪ B)
  have c2 := hV ((A ∩ B).erase i0)
  have c3 : ((A ∩ B).erase i0).card = (A ∩ B).card - 1 := card_erase_of_mem
    (mem_inter.2 ⟨hA0, hB0⟩)
  have c4 := card_union_add_card_inter A B
  have c5 : 0 < (A ∩ B).card := card_pos.2 ⟨i0, mem_inter.2 ⟨hA0, hB0⟩⟩
  omega

/-- **Rado's theorem** for linear independence. -/
theorem rado [FiniteDimensional K L] [Fintype ι] :
    ∀ (n : ℕ) (V : ι → Finset L), ∑ i, (V i).card = n → Cond K V →
      ∃ v : ι → L, (∀ i, v i ∈ V i) ∧ LinearIndependent K v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hn hV
    by_cases hbig : ∃ i0, 2 ≤ (V i0).card
    · obtain ⟨i0, h2⟩ := hbig
      obtain ⟨u, hu, hV'⟩ := exists_delete hV h2
      have hlt : ∑ i, (Function.update V i0 ((V i0).erase u) i).card < n := by
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro i _
          by_cases hi : i = i0
          · subst hi; simp [card_erase_le]
          · simp [Function.update_of_ne hi]
        · refine ⟨i0, mem_univ _, ?_⟩
          simp [card_erase_of_mem hu]
          exact ⟨u, hu⟩
      obtain ⟨v, hv, hli⟩ := ih _ hlt _ rfl hV'
      refine ⟨v, fun i => ?_, hli⟩
      have := hv i
      by_cases hi : i = i0
      · subst hi; simp at this; exact this.2
      · simpa [Function.update_of_ne hi] using this
    · push Not at hbig
      -- every set is a singleton
      have hne : ∀ i, (V i).card = 1 := by
        intro i
        have h1 : 1 ≤ finrank K (spanU K V {i}) := by simpa using hV {i}
        have h2 : finrank K (spanU K V {i}) ≤ (V i).card := by
          have e : (⋃ j ∈ ({i} : Finset ι), (V j : Set L)) = (V i : Set L) := by simp
          unfold spanU
          rw [e]
          exact finrank_span_finset_le_card (R := K) (V i)
        have := hbig i
        omega
      choose v hv using fun i => Finset.card_eq_one.1 (hne i)
      refine ⟨v, fun i => by simp [hv i], ?_⟩
      rw [linearIndependent_iff_card_eq_finrank_span]
      have hall := hV Finset.univ
      have hle : finrank K (spanU K V Finset.univ) ≤ (Set.range v).finrank K := by
        apply Submodule.finrank_mono
        apply Submodule.span_le.2
        intro z hz
        simp only [Set.mem_iUnion, mem_coe, mem_univ, true_and] at hz
        obtain ⟨i, hzi⟩ := hz
        rw [hv i] at hzi
        simp at hzi
        subst hzi
        exact Submodule.subset_span ⟨i, rfl⟩
      have hup : (Set.range v).finrank K ≤ Fintype.card ι := by
        unfold Set.finrank
        simpa using finrank_range_le_card (R := K) v
      simp only [card_univ] at hall
      omega

/-- **Rado's theorem** (Welsh's vector space form of Hall's theorem): a finite family of finite sets
of vectors, every subfamily of which spans at least as many dimensions as its size, has a linearly
independent system of representatives. -/
theorem rado_exists [FiniteDimensional K L] [Fintype ι] (V : ι → Finset L) (h : Cond K V) :
    ∃ v : ι → L, (∀ i, v i ∈ V i) ∧ LinearIndependent K v :=
  rado _ V rfl h

end Rado

end SATurday.ProofComplexity
