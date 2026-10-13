import Theory.ProofComplexity.BraunAffineFinite
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Ordinary restriction ideals and proper affine block restriction (R4 Phase 2.1, layer 7b)

Credit. Port, with proofs adapted to our `BraunAffineFinite`, of K. Braun (arXiv 2609.23015,
author's Lean development): `CoordinateRestrictionIdeal.lean` (`coordinate_restriction_coefficients`),
`OrdinaryRestrictionDimension.lean` (`ordinary_degreeSpace_finrank_le`,
`affineSubstitution_totalDegree_le`, `ordinary_affine_restriction_finrank_le`),
`AffineRestrictionIdeal.lean` (`polynomialPullback_*`, `affine_restriction_coefficients`,
`affineRestriction_image_finrank_le`) and `AffineBlockRestriction.lean` (`affineInputRank_eq`,
`affinePolynomial_unit_span_iff`, `blockRestrictionData_exists`, `affineInputRank_le`), which
layers 3 and 5 had deferred. Statements keep his quantifier shape; `affinePolynomial_unit_span_iff`
is stated for `finiteAffinePolynomial` of our layer 1b.

LOG: R4 BraunRestriction module (Phase 2.1 layer 7b)
-/

namespace SATurday.ProofComplexity.BraunLA

noncomputable section

open MvPolynomial Module
open scoped BigOperators

section CoordRestr

variable {K σ ι : Type} [Field K] [Fintype σ] [Fintype ι]

abbrev CoordinateFreeIndex (e : ι ↪ σ) := {x : σ // x ∉ Set.range e}

def coordinateRestriction (e : ι ↪ σ) :
    MvPolynomial σ K →ₐ[K] MvPolynomial (CoordinateFreeIndex e) K :=
  killCompl (f := Subtype.val) Subtype.val_injective

omit [Fintype σ] in
private theorem selected_of_support (e : ι ↪ σ) (p : MvPolynomial σ K)
    (hp : coordinateRestriction e p = 0) (d : σ →₀ ℕ) (hd : d ∈ p.support) :
    ∃ i, 1 ≤ d (e i) := by
  classical
  by_contra hn
  push Not at hn
  have hs : (d.support : Set σ) ⊆ Set.range (Subtype.val : CoordinateFreeIndex e → σ) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    rintro ⟨i, rfl⟩
    have hdi := Finsupp.mem_support_iff.mp hx
    have hi := hn i
    omega
  have hc := congrArg (fun q => q.coeff (d.comapDomain
    (Subtype.val : CoordinateFreeIndex e → σ) Subtype.val_injective.injOn)) hp
  beta_reduce at hc
  rw [coordinateRestriction, coeff_killCompl, Finsupp.mapDomain_comapDomain (Subtype.val : CoordinateFreeIndex e → σ) Subtype.val_injective d hs] at hc
  exact MvPolynomial.mem_support_iff.mp hd (by simpa using hc)

private def removedMonomial (d : σ →₀ ℕ) (i : σ) (c : K) : MvPolynomial σ K :=
  monomial (d - Finsupp.single i 1) c

omit [Fintype σ] in
private theorem removedMonomial_identity (d : σ →₀ ℕ) (i : σ) (c : K) (hi : 1 ≤ d i) :
    removedMonomial d i c * X i = monomial d c := by
  have hle : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr hi
  rw [removedMonomial, X, monomial_mul, mul_one, tsub_add_cancel_of_le hle]

omit [Fintype σ] in
private theorem removedMonomial_degree (d : σ →₀ ℕ) (i : σ) (c : K) (hi : 1 ≤ d i)
    (k : ℕ) (hk : d.sum (fun _ n => n) ≤ k) :
    (removedMonomial d i c).totalDegree ≤ k-1 := by
  have hle : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr hi
  have he := congrArg (fun a : σ →₀ ℕ => a.sum (fun _ n => n)) (tsub_add_cancel_of_le hle)
  simp [Finsupp.sum_add_index'] at he
  apply (totalDegree_monomial_le _ _).trans
  change (d - Finsupp.single i 1).sum (fun _ n => n) ≤ k-1
  omega

omit [Fintype σ] in
theorem coordinate_restriction_coefficients (e : ι ↪ σ) (p : MvPolynomial σ K) (k : ℕ)
    (hdeg : p.totalDegree ≤ k) (hp : coordinateRestriction e p = 0) :
    ∃ a : ι → MvPolynomial σ K, (∀ i, (a i).totalDegree ≤ k-1) ∧ p = ∑ i, a i * X (e i) := by
  classical
  have hsel : ∀ d : p.support, ∃ i, 1 ≤ d.val (e i) := fun d => selected_of_support e p hp d.val d.property
  choose s hs using hsel
  let q : p.support → MvPolynomial σ K := fun d => removedMonomial d.val (e (s d)) (p.coeff d.val)
  let a : ι → MvPolynomial σ K := fun i => ∑ d : p.support, if s d = i then q d else 0
  refine ⟨a, ?_, ?_⟩
  · intro i
    apply totalDegree_finsetSum_le
    intro d _
    by_cases hi : s d = i
    · simp only [hi, ite_true]
      exact removedMonomial_degree d.val (e (s d)) _ (hs d) k ((le_totalDegree d.property).trans hdeg)
    · simp [hi]
  · have hsum : (∑ i, a i * X (e i)) = ∑ d : p.support, monomial d.val (p.coeff d.val) := by
      simp only [a, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      exact removedMonomial_identity (K := K) d.val (e (s d)) (p.coeff d.val) (hs d)
    rw [hsum]
    rw [Finset.sum_coe_sort p.support (fun d : σ →₀ ℕ => monomial d (p.coeff d))]
    exact p.as_sum


end CoordRestr

section OrdDim

open scoped BigOperators

private def degreeExponentEmbedding (d k : ℕ) :
    {e : Fin d →₀ ℕ // e.sum (fun _ n => n) ≤ k} ↪ Sym (Option (Fin d)) k where
  toFun e := (Sym.equivNatSumOfFintype (Option (Fin d)) k).symm
    ⟨fun i => match i with | none => k - e.val.sum (fun _ n => n) | some j => e.val j,
     by
       simp only [Fintype.sum_option]
       rw [← Finsupp.sum_fintype e.val (fun _ n => n) (by simp)]
       exact Nat.sub_add_cancel e.property⟩
  inj' := by
    intro e f h
    have hh := (Sym.equivNatSumOfFintype (Option (Fin d)) k).symm.injective h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg (fun x => x.val (some i)) hh

theorem ordinary_degreeSpace_finrank_le (K : Type*) [Field K] (d k : ℕ) :
    Module.finrank K (restrictTotalDegree (Fin d) K k) ≤ (d + k).choose k := by
  let _ : Finite {e : Fin d →₀ ℕ // e.sum (fun _ n => n) ≤ k} :=
    Finite.of_injective (degreeExponentEmbedding d k) (degreeExponentEmbedding d k).injective
  let _ : Fintype {e : Fin d →₀ ℕ // e.sum (fun _ n => n) ≤ k} := Fintype.ofFinite _
  rw [show restrictTotalDegree (Fin d) K k =
    restrictSupport K {e | e.sum (fun _ n => n) ≤ k} from rfl]
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {e : Fin d →₀ ℕ // e.sum (fun _ n => n) ≤ k} ≤ _
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_le_of_injective (degreeExponentEmbedding d k)
    (degreeExponentEmbedding d k).injective
  simpa [Sym.card_sym_eq_choose] using h

theorem affineSubstitution_totalDegree_le {K σ τ : Type*} [Field K]
    (g : σ → MvPolynomial τ K) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (p : MvPolynomial σ K) : (aeval g p).totalDegree ≤ p.totalDegree := by
  classical
  nth_rw 1 [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [aeval_monomial]
  calc
    (algebraMap K (MvPolynomial τ K) (p.coeff e) * e.prod (fun i n => g i ^ n)).totalDegree
      ≤ (algebraMap K (MvPolynomial τ K) (p.coeff e)).totalDegree +
        (e.prod (fun i n => g i ^ n)).totalDegree := totalDegree_mul _ _
    _ ≤ 0 + e.sum (fun _ n => n) := by
      simp only [MvPolynomial.algebraMap_eq, totalDegree_C, zero_add]
      apply (totalDegree_finset_prod e.support _).trans
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e i) (hg i))
    _ ≤ p.totalDegree := by simpa using le_totalDegree he

theorem ordinary_affine_restriction_finrank_le {K σ : Type*} [Field K]
    (d k : ℕ) (U : Submodule K (MvPolynomial σ K))
    (hU : ∀ p ∈ U, p.totalDegree ≤ k)
    (g : σ → MvPolynomial (Fin d) K) (hg : ∀ i, (g i).totalDegree ≤ 1) :
    Module.finrank K (U.map (aeval g).toLinearMap) ≤ (d + k).choose k := by
  have hle : U.map (aeval g).toLinearMap ≤ restrictTotalDegree (Fin d) K k := by
    rintro p ⟨q, hq, rfl⟩
    apply (mem_restrictTotalDegree _ _ _).mpr
    exact (affineSubstitution_totalDegree_le g hg q).trans (hU q hq)
  exact (Submodule.finrank_mono hle).trans (ordinary_degreeSpace_finrank_le K d k)


end OrdDim

section AffRestr

variable {σ τ υ ι : Type} [Fintype σ] [Fintype τ] [Fintype υ] [Fintype ι]

private theorem affine_poly_ext (p q : MvPolynomial σ (ZMod 2))
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1)
    (he : ∀ x, eval x p = eval x q) : p = q := by
  classical
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero σ (ZMod 2) (p-q)
  · intro x; simp [he]
  · have hd : (p-q).totalDegree ≤ 1 := (totalDegree_sub _ _).trans (max_le hp hq)
    simp only [ZMod.card, Nat.reduceSub]
    apply (mem_restrictDegree_iff_sup σ (p-q) 1).mpr
    intro i
    change (p-q).degreeOf i ≤ 1
    exact (degreeOf_le_totalDegree _ _).trans hd

def polynomialPullback (A : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2)) :
    MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial τ (ZMod 2) :=
  aeval (fun i => finiteAffinePolynomial ((AffineMap.proj i).comp A))

omit [Fintype σ] in
private theorem polynomialPullback_X (A : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2)) (i : σ) :
    polynomialPullback A (X i) = finiteAffinePolynomial ((AffineMap.proj i).comp A) := aeval_X _ i

omit [Fintype σ] in
theorem polynomialPullback_degree (A : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2))
    (p : MvPolynomial σ (ZMod 2)) : (polynomialPullback A p).totalDegree ≤ p.totalDegree :=
  affineSubstitution_totalDegree_le _ (fun _ => finiteAffinePolynomial_degree _) p

omit [Fintype σ] in
theorem polynomialPullback_eval (A : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2))
    (p : MvPolynomial σ (ZMod 2)) (x : τ → ZMod 2) :
    eval x (polynomialPullback A p) = eval (A x) p := by
  change aeval x (aeval (fun i => finiteAffinePolynomial ((AffineMap.proj i).comp A)) p) = _
  rw [comp_aeval_apply]
  have he : (fun i => aeval x (finiteAffinePolynomial ((AffineMap.proj i).comp A))) = A x := by
    funext i
    exact finiteAffinePolynomial_eval _ x
  rw [he]
  rfl

omit [Fintype σ] in
theorem polynomialPullback_comp (A : (τ → ZMod 2) →ᵃ[ZMod 2] (σ → ZMod 2))
    (B : (υ → ZMod 2) →ᵃ[ZMod 2] (τ → ZMod 2)) :
    (polynomialPullback B).comp (polynomialPullback A) = polynomialPullback (A.comp B) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, polynomialPullback_X, polynomialPullback_X]
  apply affine_poly_ext
  · exact (polynomialPullback_degree _ _).trans (finiteAffinePolynomial_degree _)
  · exact finiteAffinePolynomial_degree _
  · intro x
    rw [polynomialPullback_eval, finiteAffinePolynomial_eval, finiteAffinePolynomial_eval]
    rfl

theorem polynomialPullback_id :
    polynomialPullback (AffineMap.id (ZMod 2) (σ → ZMod 2)) = AlgHom.id (ZMod 2) _ := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [polynomialPullback_X, AlgHom.id_apply]
  apply affine_poly_ext (hp := finiteAffinePolynomial_degree _) (hq := by simp)
  intro x
  simp [finiteAffinePolynomial_eval]

theorem polynomialPullback_inverse (E : (σ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2))
    (p : MvPolynomial σ (ZMod 2)) :
    polynomialPullback E.toAffineMap (polynomialPullback E.symm.toAffineMap p) = p := by
  have he : E.symm.toAffineMap.comp E.toAffineMap = AffineMap.id (ZMod 2) _ := by
    ext x; simp
  rw [← AlgHom.comp_apply, polynomialPullback_comp, he, polynomialPullback_id]
  rfl

def affineRestriction (e : ι ↪ σ) (E : (σ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2)) :
    MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] MvPolynomial (CoordinateFreeIndex e) (ZMod 2) :=
  (coordinateRestriction e).comp (polynomialPullback E.symm.toAffineMap)

theorem affine_restriction_coefficients (g : ι → (σ → ZMod 2) →ᵃ[ZMod 2] (ZMod 2))
    (e : ι ↪ σ) (E : (σ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2))
    (he : ∀ i x, E x (e i) = g i x) (p : MvPolynomial σ (ZMod 2)) (k : ℕ)
    (hp : p.totalDegree ≤ k) (hz : affineRestriction e E p = 0) :
    ∃ a : ι → MvPolynomial σ (ZMod 2),
      (∀ i, (a i).totalDegree ≤ k-1) ∧ p = ∑ i, a i * finiteAffinePolynomial (g i) := by
  classical
  obtain ⟨a,ha,heq⟩ := coordinate_restriction_coefficients e
    (polynomialPullback E.symm.toAffineMap p) k
    ((polynomialPullback_degree _ _).trans hp) hz
  refine ⟨fun i => polynomialPullback E.toAffineMap (a i),
    fun i => (polynomialPullback_degree _ _).trans (ha i), ?_⟩
  have hi (i : ι) : polynomialPullback E.toAffineMap (X (e i)) = finiteAffinePolynomial (g i) := by
    have hh : (AffineMap.proj (e i)).comp E.toAffineMap = g i := by
      ext x; exact he i x
    change aeval _ (X (e i)) = _
    rw [aeval_X, hh]
  have hh := congrArg (polynomialPullback E.toAffineMap) heq
  rw [polynomialPullback_inverse, map_sum] at hh
  simpa only [map_mul, hi] using hh

omit [Fintype σ] [Fintype ι] in
theorem coordinateRestriction_degree (e : ι ↪ σ) (p : MvPolynomial σ (ZMod 2)) :
    (coordinateRestriction e p).totalDegree ≤ p.totalDegree := by
  classical
  unfold coordinateRestriction MvPolynomial.killCompl
  apply affineSubstitution_totalDegree_le
  intro i
  split <;> simp

omit [Fintype ι] in
theorem affineRestriction_degree (e : ι ↪ σ)
    (E : (σ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2)) (p : MvPolynomial σ (ZMod 2)) :
    (affineRestriction e E p).totalDegree ≤ p.totalDegree :=
  (coordinateRestriction_degree e _).trans (polynomialPullback_degree _ p)

private theorem finite_degreeSpace_finrank_le (k : ℕ) :
    Module.finrank (ZMod 2) (restrictTotalDegree σ (ZMod 2) k) ≤
      (Fintype.card σ+k).choose k := by
  classical
  let e := Fintype.equivFin σ
  let T : restrictTotalDegree σ (ZMod 2) k →ₗ[ZMod 2]
      restrictTotalDegree (Fin (Fintype.card σ)) (ZMod 2) k :=
    { toFun := fun p => ⟨rename e p.val, (mem_restrictTotalDegree _ _ _).mpr
        ((totalDegree_rename_le e p.val).trans ((mem_restrictTotalDegree _ _ _).mp p.property))⟩
      map_add' := by intro p q; apply Subtype.ext; exact map_add (rename e) p.val q.val
      map_smul' := by intro c p; apply Subtype.ext; exact map_smul (rename e) c p.val }
  have hi : Function.Injective T := by
    intro p q hpq
    apply Subtype.ext
    exact (rename_injective e e.injective) (congrArg Subtype.val hpq)
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans
    (ordinary_degreeSpace_finrank_le (ZMod 2) _ k)

theorem coordinateFreeIndex_card (e : ι ↪ σ) :
    Nat.card (CoordinateFreeIndex e) = Fintype.card σ-Fintype.card ι := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {x : σ // ¬x ∈ Set.range e} = _
  rw [Fintype.card_subtype_compl]
  congr 1
  exact (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm

theorem affineRestriction_image_finrank_le (e : ι ↪ σ)
    (E : (σ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2))
    (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (k : ℕ)
    (hU : ∀ p ∈ U, p.totalDegree ≤ k) :
    Module.finrank (ZMod 2) (U.map (affineRestriction e E).toLinearMap) ≤
      (Fintype.card σ-Fintype.card ι+k).choose k := by
  classical
  have hle : U.map (affineRestriction e E).toLinearMap ≤
      restrictTotalDegree (CoordinateFreeIndex e) (ZMod 2) k := by
    rintro p ⟨q,hq,rfl⟩
    exact (mem_restrictTotalDegree _ _ _).mpr ((affineRestriction_degree e E q).trans (hU q hq))
  have hb := (Submodule.finrank_mono hle).trans
    (finite_degreeSpace_finrank_le (σ := CoordinateFreeIndex e) k)
  have hc : Fintype.card (CoordinateFreeIndex e) = Fintype.card σ-Fintype.card ι := by
    simpa only [Nat.card_eq_fintype_card] using coordinateFreeIndex_card e
  simpa only [hc] using hb


end AffRestr

section Block

variable {σ ι : Type} [Fintype σ] [Fintype ι]

abbrev AffineInputMap (σ : Type) := (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2

def affineInputRank (g : ι → AffineInputMap σ) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun i => finiteAffinePolynomial (g i))))

private theorem finiteAffinePolynomial_const_one :
    finiteAffinePolynomial (AffineMap.const (ZMod 2) (σ → ZMod 2) 1) = 1 := by
  simp [finiteAffinePolynomial]

theorem affinePolynomial_unit_span_iff (g : ι → AffineInputMap σ) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (fun i => finiteAffinePolynomial (g i))) ↔
    AffineMap.const (ZMod 2) (σ → ZMod 2) 1 ∈ Submodule.span (ZMod 2) (Set.range g) := by
  classical
  rw [Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    apply finiteAffinePolynomial_injective
    simpa only [map_sum, map_smul, finiteAffinePolynomial_const_one] using hc
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    have he := congrArg finiteAffinePolynomial hc
    simpa only [map_sum, map_smul, finiteAffinePolynomial_const_one] using he

omit [Fintype ι] in
theorem affineInputRank_eq (g : ι → AffineInputMap σ) :
    affineInputRank g = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) := by
  let S := Submodule.span (ZMod 2) (Set.range g)
  let T := finiteAffinePolynomial.comp S.subtype
  have hi : Function.Injective T := by
    intro a b h
    apply Subtype.ext
    exact finiteAffinePolynomial_injective h
  have he : T.range = S.map finiteAffinePolynomial := by
    ext p
    constructor
    · rintro ⟨a,rfl⟩; exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
  have hs : S.map finiteAffinePolynomial =
      Submodule.span (ZMod 2) (Set.range (fun i => finiteAffinePolynomial (g i))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  unfold affineInputRank
  rw [← hs, ← he]
  exact LinearMap.finrank_range_of_inj hi

structure BlockRestrictionData (g : ι → AffineInputMap σ) where
  embedding : Fin (affineInputRank g) ↪ σ
  coordinates : (σ → ZMod 2) ≃ᵃ[ZMod 2] (σ → ZMod 2)
  zeroFlat : ∀ x, (∀ j, coordinates x (embedding j) = 0) ↔ ∀ i, g i x = 0
  literal : ∀ p : MvPolynomial σ (ZMod 2), ∀ k : ℕ, p.totalDegree ≤ k →
    affineRestriction embedding coordinates p = 0 →
    ∃ a : ι → MvPolynomial σ (ZMod 2),
      (∀ i, (a i).totalDegree ≤ k-1) ∧ p = ∑ i, a i * finiteAffinePolynomial (g i)

theorem blockRestrictionData_exists (g : ι → AffineInputMap σ)
    (hproper : (1 : MvPolynomial σ (ZMod 2)) ∉
      Submodule.span (ZMod 2) (Set.range (fun i => finiteAffinePolynomial (g i)))) :
    Nonempty (BlockRestrictionData g) := by
  classical
  let S := Submodule.span (ZMod 2) (Set.range g)
  let _ : FiniteDimensional (ZMod 2) S := FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range g)
  let B : Basis (Fin (affineInputRank g)) (ZMod 2) S :=
    (Module.finBasis (ZMod 2) S).reindex (finCongr (affineInputRank_eq g).symm)
  let G := fun j => (B j).val
  have hG : LinearIndependent (ZMod 2) G :=
    B.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hc : ∀ j, ∃ c : ι → ZMod 2, ∑ i, c i • g i = G j := by
    intro j
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp (B j).property
  choose c hc using hc
  have hd : ∀ i, ∃ d : Fin (affineInputRank g) → ZMod 2, ∑ j, d j • G j = g i := by
    intro i
    let v : S := ⟨g i,Submodule.subset_span (Set.mem_range_self i)⟩
    refine ⟨fun j => B.repr v j,?_⟩
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using congrArg Subtype.val (B.sum_repr v)
  choose d hd using hd
  have hGS : Submodule.span (ZMod 2) (Set.range G) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩; exact (B j).property
  have hGP : AffineMap.const (ZMod 2) (σ → ZMod 2) 1 ∉ Submodule.span (ZMod 2) (Set.range G) := by
    intro hm
    exact hproper ((affinePolynomial_unit_span_iff g).mpr (hGS hm))
  obtain ⟨e,E,he⟩ := finite_affine_coordinate_completion G hG hGP
  refine ⟨{ embedding := e, coordinates := E, zeroFlat := ?_, literal := ?_ }⟩
  · intro x
    have hzero : (∀ j, G j x = 0) ↔ ∀ i, g i x = 0 := by
      let ev : AffineInputMap σ →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun f => f x, map_add' := by intros; rfl, map_smul' := by intros; rfl }
      constructor
      · intro hx i
        have hv := congrArg ev (hd i)
        simp only [map_sum,map_smul] at hv
        simpa [ev,hx] using hv.symm
      · intro hx j
        have hv := congrArg ev (hc j)
        simp only [map_sum,map_smul] at hv
        simpa [ev,hx] using hv.symm
    simpa only [he] using hzero
  · intro p k hp hz
    obtain ⟨a,ha,hpA⟩ := affine_restriction_coefficients G e E he p k hp hz
    let a' : ι → MvPolynomial σ (ZMod 2) := fun i => ∑ j, c j i • a j
    refine ⟨a',?_,?_⟩
    · intro i
      apply totalDegree_finsetSum_le
      intro j _
      exact (totalDegree_smul_le _ _).trans (ha j)
    · rw [hpA]
      simp only [a',Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have hpoly := congrArg finiteAffinePolynomial (hc j)
      simp only [map_sum,map_smul] at hpoly
      rw [← hpoly, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [smul_eq_C_mul]
      ring

theorem affineInputRank_le (g : ι → AffineInputMap σ)
    (hproper : (1 : MvPolynomial σ (ZMod 2)) ∉
      Submodule.span (ZMod 2) (Set.range (fun i => finiteAffinePolynomial (g i)))) :
    affineInputRank g ≤ Fintype.card σ := by
  obtain ⟨R⟩ := blockRestrictionData_exists g hproper
  simpa using Fintype.card_le_of_embedding R.embedding


end Block

end

end SATurday.ProofComplexity.BraunLA
