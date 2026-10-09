import Theory.ProofComplexity.Closure
import Theory.ProofComplexity.Rado

/-!
# Safe forms have one pivot variable per block (EGI Theorem 3.1)

If independent forms `f_1..f_k` span a safe space, there are `k` variables in pairwise distinct
blocks such that the `k × k` matrix `(f_i(z_j))` has independent columns. Proof: the condition of
Rado's theorem with deficiency `|B| - k` for the column vectors, from safety and rank-nullity.

LOG: R4 ClosurePivot module (safe implies transversal)
-/

namespace SATurday.ProofComplexity

namespace Closure

noncomputable section

open Classical
open Module Finset

variable {K ι β : Type*} [Field K] [DecidableEq β] [DecidableEq ι] (b : ι → β)

/-- The column of the variable `w` in the coefficient matrix of `f`. -/
def col {k : ℕ} (f : Fin k → (ι →₀ K)) (w : ι) : Fin k → K := fun i => f i w

theorem k_le_blocks {k : ℕ} (f : Fin k → (ι →₀ K)) (hli : LinearIndependent K f)
    (hsafe : Safe b (Submodule.span K (Set.range f))) (B : Finset β)
    (hB : ∀ i, supp b (f i) ⊆ B) : k ≤ B.card := by
  haveI : FiniteDimensional K (Submodule.span K (Set.range f)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range f)
  by_contra h
  push Not at h
  have hle : Submodule.span K (Set.range f) ≤ U b B := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact (mem_U b).2 (hB i)
  have hk : finrank K (Submodule.span K (Set.range f)) = k := by
    rw [finrank_span_eq_card hli]; simp
  obtain ⟨H, hH1, hH2⟩ := exists_dang b (Submodule.span K (Set.range f)) B hle (by omega)
  exact hsafe H hH1 hH2

theorem col_bound {k : ℕ} (f : Fin k → (ι →₀ K)) (hli : LinearIndependent K f)
    (hsafe : Safe b (Submodule.span K (Set.range f))) (Vars : Finset ι)
    (hV : ∀ i, (f i).support ⊆ Vars) (T : Finset β) (hT : T ⊆ Vars.image b) :
    T.card + k ≤ finrank K (Submodule.span K
      (((Vars.filter fun w => b w ∈ T).image (col f) : Finset (Fin k → K)) : Set (Fin k → K))) +
      (Vars.image b).card := by
  haveI : FiniteDimensional K (Submodule.span K (Set.range f)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range f)
  set B := Vars.image b with hB
  set VT := Vars.filter fun w => b w ∈ T with hVT
  let A : Matrix VT (Fin k) K := fun w i => f i w.1
  have h1 : A.rank = finrank K (Submodule.span K (Set.range A.row)) := A.rank_eq_finrank_span_row
  have hrow : Set.range A.row = ((VT.image (col f) : Finset (Fin k → K)) : Set (Fin k → K)) := by
    ext x
    simp only [Set.mem_range, coe_image, Set.mem_image, mem_coe]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrk : A.rank = finrank K (LinearMap.range A.mulVecLin) := rfl
  rw [Module.finrank_fin_fun] at h2
  have hsupp : ∀ i, supp b (f i) ⊆ B := by
    intro i c hc
    obtain ⟨w, hw, rfl⟩ := (mem_supp b).1 hc
    exact mem_image_of_mem b (hV i (Finsupp.mem_support_iff.2 hw))
  have hkb := k_le_blocks b f hli hsafe B hsupp
  -- kernel dimension
  have hker : finrank K (LinearMap.ker A.mulVecLin) ≤ (B \ T).card := by
    let E := Fintype.linearCombination K f
    have hEinj : Function.Injective E :=
      linearIndependent_iff_injective_fintypeLinearCombination.mp hli
    let N : Submodule K (ι →₀ K) := Submodule.span K (Set.range f) ⊓ U b (B \ T)
    have hmap : ∀ c ∈ LinearMap.ker A.mulVecLin, E c ∈ N := by
      intro c hc
      refine ⟨?_, ?_⟩
      · rw [Fintype.linearCombination_apply]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · refine (mem_U b).2 ?_
        intro x hx
        obtain ⟨w, hw, rfl⟩ := (mem_supp b).1 hx
        have hEw : E c w = ∑ i, c i * f i w := by
          rw [Fintype.linearCombination_apply, Finsupp.finset_sum_apply]
          simp [Finsupp.smul_apply]
        have hwV : w ∈ Vars := by
          by_contra hn
          apply hw
          rw [hEw]
          apply Finset.sum_eq_zero
          intro i _
          have : f i w = 0 := by
            by_contra hne
            exact hn (hV i (Finsupp.mem_support_iff.2 hne))
          simp [this]
        refine mem_sdiff.2 ⟨mem_image_of_mem b hwV, fun hbT => hw ?_⟩
        have hwVT : w ∈ VT := mem_filter.2 ⟨hwV, hbT⟩
        have := congrFun (LinearMap.mem_ker.1 hc) ⟨w, hwVT⟩
        rw [hEw]
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, mul_comm] using this
    let R : LinearMap.ker A.mulVecLin →ₗ[K] N :=
      (E.restrict (p := LinearMap.ker A.mulVecLin) (q := N) hmap)
    have hRinj : Function.Injective R := by
      intro x y hxy
      apply Subtype.ext
      apply hEinj
      exact congrArg Subtype.val hxy
    have hle1 := LinearMap.finrank_le_finrank_of_injective hRinj
    have hle2 : finrank K N ≤ (B \ T).card := by
      by_contra hc
      push Not at hc
      obtain ⟨H, hH1, hH2⟩ := exists_dang b N (B \ T) inf_le_right hc
      exact hsafe H (fun f hf => (hH1 hf).1) hH2
    omega
  have hcard : (B \ T).card = B.card - T.card := card_sdiff_of_subset hT
  have hTB : T.card ≤ B.card := card_le_card hT
  rw [hrow] at h1
  generalize finrank K ↥(Submodule.span K (((VT.image (col f) : Finset (Fin k → K)) : Set (Fin k → K)))) = r at *
  generalize finrank K ↥(LinearMap.range A.mulVecLin) = s at *
  generalize finrank K ↥(LinearMap.ker A.mulVecLin) = t at *
  omega

/-- **Safe forms have pivots in distinct blocks** (EGI Theorem 3.1, (1) implies (3)). -/
theorem pivot {k : ℕ} (f : Fin k → (ι →₀ K)) (hli : LinearIndependent K f)
    (hsafe : Safe b (Submodule.span K (Set.range f))) :
    ∃ z : Fin k → ι, Function.Injective (b ∘ z) ∧ LinearIndependent K (fun j => col f (z j)) := by
  set Vars : Finset ι := Finset.univ.biUnion (fun i => (f i).support) with hVars
  have hV : ∀ i, (f i).support ⊆ Vars := fun i => by rw [hVars]; exact subset_biUnion_of_mem (fun i => (f i).support) (mem_univ i)
  set B : Finset β := Vars.image b with hB
  have hsupp : ∀ i, supp b (f i) ⊆ B := by
    intro i c hc
    obtain ⟨w, hw, rfl⟩ := (mem_supp b).1 hc
    exact mem_image_of_mem b (hV i (Finsupp.mem_support_iff.2 hw))
  have hkb := k_le_blocks b f hli hsafe B hsupp
  let Vc : ↥B → Finset (Fin k → K) := fun c => (Vars.filter fun w => b w = c.1).image (col f)
  have hCond : Rado.Cond K (B.card - k) Vc := by
    intro A
    have hT : A.map (Function.Embedding.subtype _) ⊆ Vars.image b := by
      intro x hx
      obtain ⟨c, _, rfl⟩ := mem_map.1 hx
      exact c.2
    have hcb := col_bound b f hli hsafe Vars hV _ hT
    have hspan : Rado.spanU K Vc A = Submodule.span K
        (((Vars.filter fun w => b w ∈ A.map (Function.Embedding.subtype _)).image (col f) :
          Finset (Fin k → K)) : Set (Fin k → K)) := by
      unfold Rado.spanU
      congr 1
      ext x
      simp only [Set.mem_iUnion, Finset.mem_coe, Vc, mem_image, mem_filter, mem_map, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨c, hc, w, ⟨hwV, hwb⟩, rfl⟩
        exact ⟨w, ⟨hwV, c, hc, hwb.symm⟩, rfl⟩
      · rintro ⟨w, ⟨hwV, c, hc, hcb'⟩, rfl⟩
        exact ⟨c, hc, w, ⟨hwV, hcb'.symm⟩, rfl⟩
    rw [hspan]
    rw [card_map] at hcb
    have hd : (Vars.image b).card = B.card := by rw [hB]
    omega
  obtain ⟨S, hS, v, hv, hli'⟩ := Rado.rado_def (K := K) (d := B.card - k) _ Vc rfl hCond
  rw [Fintype.card_coe] at hS
  have hSk : S.card ≤ k := by
    have := hli'.linearIndependent.fintype_card_le_finrank
    simpa using this
  have hcard : S.card = k := by omega
  have hex : ∀ c ∈ S, ∃ w, w ∈ Vars ∧ b w = c.1 ∧ col f w = v c := by
    intro c hc
    obtain ⟨w, hw, hwc⟩ := mem_image.1 (hv c hc)
    exact ⟨w, (mem_filter.1 hw).1, (mem_filter.1 hw).2, hwc⟩
  choose W hW using hex
  let e : Fin k ≃ S := (Finset.equivFinOfCardEq hcard).symm
  refine ⟨fun j => W (e j).1 (e j).2, ?_, ?_⟩
  · intro j j' h
    have h1 : (e j).1.1 = (e j').1.1 := by
      have := h
      simp only [Function.comp] at this
      rw [(hW _ (e j).2).2.1, (hW _ (e j').2).2.1] at this
      exact this
    exact e.injective (Subtype.ext (Subtype.ext h1))
  · have := hli'.linearIndependent.comp e e.injective
    convert this using 1
    funext j
    exact (hW _ (e j).2).2.2

end

end Closure

end SATurday.ProofComplexity
