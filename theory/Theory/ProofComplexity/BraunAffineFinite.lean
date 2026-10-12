import Theory.ProofComplexity.BraunAffineForm
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Data.Fintype.EquivFin

/-!
# Affine maps on finite coordinate types, and coordinate completion (R4 Phase 2.1, layer 1b)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`FiniteAffinePolynomial.lean` (`finiteAffinePolynomial_eval`, `_degree`, `_injective`, `_fin`),
`FiniteAffineSpan.lean` (`finite_affine_vanishing_coefficients`, `finite_affine_unit_coefficients`),
`FiniteAffineCoordinates.lean` (`finite_affine_coordinate_completion`) and
`AffineCoordinates.lean` (`affine_coordinate_completion`, `affineFlatParam_injective`,
`affineFlatParam_range`, `affineFreeIndex_card`). Statements keep his shape.

LOG: R4 BraunAffineFinite module (Phase 2.1 layer 1b)
-/

namespace SATurday.ProofComplexity.BraunLA

noncomputable section

open scoped BigOperators
open Module

section FinitePoly

variable {K σ : Type} [Field K] [Fintype σ]

open Classical in
/-- Ordinary polynomial of an affine map on `σ → K` for a finite coordinate type `σ`. -/
def finiteAffinePolynomial : ((σ → K) →ᵃ[K] K) →ₗ[K] MvPolynomial σ K where
  toFun f := MvPolynomial.C (f 0) +
    ∑ i, f.linear (fun j => if i = j then 1 else 0) • MvPolynomial.X i
  map_add' f g := by
    simp [map_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c f := by
    simp [smul_add, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, map_mul, mul_assoc]

theorem finiteAffinePolynomial_eval (f : (σ → K) →ᵃ[K] K) (x : σ → K) :
    MvPolynomial.eval x (finiteAffinePolynomial f) = f x := by
  classical
  have h := congrFun f.decomp x
  change f x = f.linear x + f 0 at h
  rw [LinearMap.pi_apply_eq_sum_univ f.linear x] at h
  simpa [finiteAffinePolynomial, MvPolynomial.smul_eq_C_mul, add_comm, mul_comm] using h.symm

theorem finiteAffinePolynomial_degree (f : (σ → K) →ᵃ[K] K) :
    (finiteAffinePolynomial f).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (by simp)

theorem finiteAffinePolynomial_injective :
    Function.Injective (finiteAffinePolynomial (K := K) (σ := σ)) := by
  intro f g h
  ext x
  rw [← finiteAffinePolynomial_eval, ← finiteAffinePolynomial_eval, h]

theorem finiteAffinePolynomial_fin {n : ℕ} (f : (Fin n → K) →ᵃ[K] K) :
    finiteAffinePolynomial f = affinePolynomial (affineFormOfMap f) := by
  simp only [finiteAffinePolynomial, LinearMap.coe_mk, AddHom.coe_mk, affinePolynomial,
    affineFormOfMap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply congrArg f.linear
  funext j
  by_cases he : i = j <;> simp [he]

end FinitePoly

section FiniteSpan

variable {K σ ι : Type} [Field K] [Fintype σ] [Fintype ι]

/-- Reindex a finite coordinate type by `Fin (card σ)`. -/
private def reindexMap : (Fin (Fintype.card σ) → K) →ₗ[K] (σ → K) where
  toFun x i := x (Fintype.equivFin σ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem reindexMap_surjective : Function.Surjective (reindexMap (K := K) (σ := σ)) :=
  fun x => ⟨fun j => x ((Fintype.equivFin σ).symm j), by ext i; simp [reindexMap]⟩

private def reindexAff (f : (σ → K) →ᵃ[K] K) : (Fin (Fintype.card σ) → K) →ᵃ[K] K :=
  f.comp reindexMap.toAffineMap

private theorem coefficient_transfer
    (f : (σ → K) →ᵃ[K] K) (g : ι → (σ → K) →ᵃ[K] K) (c : ι → K)
    (hc : affineFormOfMap (reindexAff f) = ∑ i, c i • affineFormOfMap (reindexAff (g i))) :
    f = ∑ i, c i • g i := by
  ext x
  obtain ⟨y, hy⟩ := reindexMap_surjective (K := K) x
  have he := congrArg (affineEvaluation y) hc
  simp only [map_sum, map_smul, affineEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    affineFormOfMap_value, reindexAff, AffineMap.comp_apply] at he
  let ev : ((σ → K) →ᵃ[K] K) →ₗ[K] K :=
    { toFun := fun a => a x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change ev f = ev (∑ i, c i • g i)
  rw [map_sum]
  simp only [map_smul]
  simpa [ev, hy, smul_eq_mul] using he

theorem finite_affine_vanishing_coefficients (g : ι → (σ → K) →ᵃ[K] K)
    (x : σ → K) (hx : ∀ i, g i x = 0) (f : (σ → K) →ᵃ[K] K)
    (hf : ∀ y, (∀ i, g i y = 0) → f y = 0) :
    ∃ c : ι → K, f = ∑ i, c i • g i := by
  obtain ⟨x', hx'⟩ := reindexMap_surjective (K := K) x
  obtain ⟨c, hc⟩ := affine_vanishing_coefficients
    (fun i => affineFormOfMap (reindexAff (g i))) x'
    (fun i => by simpa [affineFormOfMap_value, reindexAff, hx'] using hx i)
    (affineFormOfMap (reindexAff f)) (by
      intro y hy
      apply (show affineValue (affineFormOfMap (reindexAff f)) y =
          f (reindexMap y) from affineFormOfMap_value _ _).trans
      apply hf
      intro i
      simpa [affineFormOfMap_value, reindexAff] using hy i)
  exact ⟨c, coefficient_transfer f g c hc⟩

theorem finite_affine_unit_coefficients (g : ι → (σ → K) →ᵃ[K] K)
    (h : ¬ ∃ x : σ → K, ∀ i, g i x = 0) :
    ∃ c : ι → K, AffineMap.const K (σ → K) 1 = ∑ i, c i • g i := by
  obtain ⟨c, hc⟩ := affine_inconsistent_unit_coefficients
    (fun i => affineFormOfMap (reindexAff (g i))) (by
      rintro ⟨x, hx⟩
      apply h
      refine ⟨reindexMap x, fun i => ?_⟩
      simpa [affineFormOfMap_value, reindexAff] using hx i)
  refine ⟨c, coefficient_transfer _ g c ?_⟩
  convert hc using 1
  funext i
  cases i <;> simp [affineFormOfMap, reindexAff, affineUnit]

end FiniteSpan

section Coordinates

variable {K σ ι : Type} [Field K] [Fintype σ] [Fintype ι]

private def affLinear : ((σ → K) →ᵃ[K] K) →ₗ[K] Module.Dual K (σ → K) where
  toFun f := f.linear
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype σ] in
private theorem affLinear_injOn (S : Submodule K ((σ → K) →ᵃ[K] K))
    (x0 : σ → K) (hx : ∀ f ∈ S, f x0 = 0) :
    Set.InjOn affLinear (S : Set ((σ → K) →ᵃ[K] K)) := by
  intro f hf g hg hfg
  have hlin : f.linear = g.linear := hfg
  have h0 : f 0 = g 0 := by
    have hf0 := congrFun f.decomp x0
    have hg0 := congrFun g.decomp x0
    change f x0 = f.linear x0 + f 0 at hf0
    change g x0 = g.linear x0 + g 0 at hg0
    rw [hx f hf, hlin] at hf0
    rw [hx g hg] at hg0
    exact add_left_cancel (hf0.symm.trans hg0)
  ext x
  have hf0 := congrFun f.decomp x
  have hg0 := congrFun g.decomp x
  change f x = f.linear x + f 0 at hf0
  change g x = g.linear x + g 0 at hg0
  rw [hf0, hg0, hlin, h0]

omit [Fintype ι] in
/-- Extend an independent family of functionals to a basis of the dual, with an embedding of the
index set into the coordinates. -/
theorem extend_dual_family (L : ι → Module.Dual K (σ → K)) (hL : LinearIndependent K L) :
    ∃ (B : Basis σ K (Module.Dual K (σ → K))) (e : ι ↪ σ), ∀ i, B (e i) = L i := by
  classical
  let I := hL.linearIndepOn_id.extend (Set.subset_univ _)
  let b : Basis I K (Module.Dual K (σ → K)) := Basis.extend hL.linearIndepOn_id
  let re := b.indexEquiv (Pi.basisFun K σ).dualBasis
  let emb (i : ι) : I := ⟨L i, hL.linearIndepOn_id.subset_extend _ (Set.mem_range_self i)⟩
  have hi : Function.Injective emb := fun _ _ h => hL.injective (congrArg Subtype.val h)
  refine ⟨b.reindex re, ⟨fun i => re (emb i), re.injective.comp hi⟩, ?_⟩
  intro i
  rw [Basis.reindex_apply]
  simp only [Function.Embedding.coeFn_mk, re.symm_apply_apply]
  exact Basis.extend_apply_self hL.linearIndepOn_id (emb i)

/-- Braun's `finite_affine_coordinate_completion`: a proper independent family of affine maps is
part of an affine coordinate system. -/
theorem finite_affine_coordinate_completion (g : ι → (σ → K) →ᵃ[K] K)
    (hg : LinearIndependent K g)
    (hproper : AffineMap.const K (σ → K) 1 ∉ Submodule.span K (Set.range g)) :
    ∃ (e : ι ↪ σ) (E : (σ → K) ≃ᵃ[K] (σ → K)), ∀ i x, E x (e i) = g i x := by
  classical
  have hz : ∃ x, ∀ i, g i x = 0 := by
    by_contra hn
    obtain ⟨c, hc⟩ := finite_affine_unit_coefficients g hn
    exact hproper ((Submodule.mem_span_range_iff_exists_fun K).mpr ⟨c, hc.symm⟩)
  obtain ⟨x0, hx0⟩ := hz
  let ev : ((σ → K) →ᵃ[K] K) →ₗ[K] K :=
    { toFun := fun f => f x0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hS : Submodule.span K (Set.range g) ≤ ev.ker :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx0 i)
  have hL := hg.map_injOn affLinear (affLinear_injOn _ x0 fun f hf => hS hf)
  obtain ⟨B, e, he⟩ := extend_dual_family (fun i => (g i).linear) hL
  let T : (σ → K) ≃ₗ[K] (σ → K) := (Module.evalEquiv K (σ → K)).trans B.dualBasis.equivFun
  refine ⟨e, (AffineEquiv.vaddConst K x0).symm.trans T.toAffineEquiv, fun i x => ?_⟩
  change T (x - x0) (e i) = g i x
  have ht : T (x - x0) (e i) = (g i).linear (x - x0) := by
    simp [T, Basis.dualBasis_equivFun, he]
  rw [ht]
  simpa [hx0 i] using (g i).linearMap_vsub x x0

end Coordinates

section FinCoordinates

variable {K : Type*} [Field K] {n : ℕ}

private def coeffDual : (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K) where
  toFun a :=
    { toFun := fun x => ∑ i, a i * x i
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_left_comm] }
  map_add' := by intro a b; ext x; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intro c a; ext x; simp [Finset.mul_sum, mul_assoc]

private theorem coeffDual_injective : Function.Injective (coeffDual (K := K) (n := n)) := by
  intro a b h
  funext i
  have hi := LinearMap.congr_fun h (fun j => if i = j then 1 else 0)
  simpa [coeffDual, mul_ite] using hi

/-- Variant of `extend_dual_family` for `Fin n` with an arbitrary index type. -/
private theorem extend_dual_family_fin {ι : Type*} (L : ι → Module.Dual K (Fin n → K))
    (hL : LinearIndependent K L) :
    ∃ (B : Basis (Fin n) K (Module.Dual K (Fin n → K))) (e : ι ↪ Fin n), ∀ i, B (e i) = L i := by
  let I := hL.linearIndepOn_id.extend (Set.subset_univ _)
  let b : Basis I K (Module.Dual K (Fin n → K)) := Basis.extend hL.linearIndepOn_id
  let re := b.indexEquiv (Pi.basisFun K (Fin n)).dualBasis
  let emb (i : ι) : I := ⟨L i, hL.linearIndepOn_id.subset_extend _ (Set.mem_range_self i)⟩
  have hi : Function.Injective emb := fun _ _ h => hL.injective (congrArg Subtype.val h)
  refine ⟨b.reindex re, ⟨fun i => re (emb i), re.injective.comp hi⟩, fun i => ?_⟩
  rw [Basis.reindex_apply]
  simp only [Function.Embedding.coeFn_mk, re.symm_apply_apply]
  exact Basis.extend_apply_self hL.linearIndepOn_id (emb i)

/-- Braun's `affine_coordinate_completion` for coefficient forms on `Fin n`. -/
theorem affine_coordinate_completion {ι : Type*} (g : ι → AffineForm K n)
    (hg : LinearIndependent K g)
    (hproper : affineUnit none ∉ Submodule.span K (Set.range g)) :
    ∃ (e : ι ↪ Fin n) (E : (Fin n → K) ≃ᵃ[K] (Fin n → K)),
      ∀ i x, E x (e i) = affineValue (g i) x := by
  let L : ι → Module.Dual K (Fin n → K) := fun i => coeffDual (affineLinearPart (g i))
  have hL : LinearIndependent K L :=
    (affine_independent_linearParts g hg hproper).map' coeffDual
      (LinearMap.ker_eq_bot.mpr coeffDual_injective)
  obtain ⟨B, e, he⟩ := extend_dual_family_fin L hL
  obtain ⟨x0, hx0⟩ := affine_proper_common_zero (Submodule.span K (Set.range g)) hproper
  let T : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Module.evalEquiv K (Fin n → K)).trans B.dualBasis.equivFun
  refine ⟨e, (AffineEquiv.vaddConst K x0).symm.trans T.toAffineEquiv, fun i x => ?_⟩
  have ht : T (x - x0) (e i) = L i (x - x0) := by
    simp [T, Basis.dualBasis_equivFun, he]
  change T (x - x0) (e i) = affineValue (g i) x
  rw [ht]
  have hz := hx0 _ (Submodule.subset_span (Set.mem_range_self i))
  simp only [affineValue] at hz
  change (∑ j, g i (some j) * (x j - x0 j)) = _
  simp only [mul_sub, Finset.sum_sub_distrib, affineValue]
  have hh : -(∑ j, g i (some j) * x0 j) = g i none :=
    neg_eq_iff_add_eq_zero.mpr (by simpa [add_comm] using hz)
  rw [sub_eq_add_neg, hh, add_comm]

/-- Indices not hit by the designated coordinates. -/
abbrev AffineFreeIndex {ι : Type*} (e : ι ↪ Fin n) := {j : Fin n // j ∉ Set.range e}

/-- Extend a free-coordinate vector by zero on the designated coordinates. -/
def affineZeroExtend {ι : Type*} (e : ι ↪ Fin n) :
    (AffineFreeIndex e → K) →ₗ[K] (Fin n → K) := by
  classical
  exact
    { toFun := fun y j => if h : j ∈ Set.range e then 0 else y ⟨j, h⟩
      map_add' := by
        intro y z; funext j
        by_cases h : j ∈ Set.range e <;> simp only [h, dite_true, dite_false, Pi.add_apply, add_zero]
      map_smul' := by
        intro c y; funext j
        by_cases h : j ∈ Set.range e <;>
          simp only [h, dite_true, dite_false, Pi.smul_apply, smul_zero, RingHom.id_apply] }

/-- Parametrization of the zero flat by the free coordinates. -/
def affineFlatParam {ι : Type*} (e : ι ↪ Fin n) (E : (Fin n → K) ≃ᵃ[K] (Fin n → K)) :
    (AffineFreeIndex e → K) →ᵃ[K] (Fin n → K) :=
  E.symm.toAffineMap.comp (affineZeroExtend e).toAffineMap

theorem affineFlatParam_injective {ι : Type*} (e : ι ↪ Fin n)
    (E : (Fin n → K) ≃ᵃ[K] (Fin n → K)) : Function.Injective (affineFlatParam e E) := by
  classical
  intro y z h
  have hh : affineZeroExtend e y = affineZeroExtend e z := E.symm.injective h
  funext j
  have hv := congrFun hh j.val
  simpa only [affineZeroExtend, LinearMap.coe_mk, AddHom.coe_mk, dif_neg j.property] using hv

theorem affineFlatParam_range {ι : Type*} (g : ι → AffineForm K n)
    (e : ι ↪ Fin n) (E : (Fin n → K) ≃ᵃ[K] (Fin n → K))
    (he : ∀ i x, E x (e i) = affineValue (g i) x) :
    Set.range (affineFlatParam e E) = {x | ∀ i, affineValue (g i) x = 0} := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [← he]
    change E (E.symm (affineZeroExtend e y)) (e i) = 0
    rw [E.apply_symm_apply]
    simp [affineZeroExtend]
  · intro hx
    refine ⟨fun j => E x j.val, E.injective ?_⟩
    change E (E.symm (affineZeroExtend e (fun j => E x j.val))) = E x
    rw [E.apply_symm_apply]
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      simp [affineZeroExtend, he, hx i]
    · simp only [affineZeroExtend, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hj]

theorem affineFreeIndex_card {r : ℕ} (e : Fin r ↪ Fin n) :
    Nat.card (AffineFreeIndex e) = n - r := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {j : Fin n // ¬j ∈ Set.range e} = n - r
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  exact (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm.trans (Fintype.card_fin r)

end FinCoordinates

end

end SATurday.ProofComplexity.BraunLA
