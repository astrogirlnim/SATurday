import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Ring

/-!
# Affine coefficient forms and their polynomial interface (Ladder Rung R4, Phase 2.1, layer 1a)

Credit. This file ports, in our own words and proofs, the statements of K. Braun, bit pigeonhole
lower bound for dag like resolution over parities (arXiv 2609.23015), as formalized in the
author's Lean development: `AffineForm.lean` (`affinePolynomial_eval`, `affinePolynomial_degree`,
`affineValue_ext`, `affinePolynomial_injective`, `affineFormOfMap_value`, `affinePolynomial_unit`)
and `AffineSystemLinearAlgebra.lean` (`affine_proper_common_zero`, `affine_vanishing_mem_span`,
`affine_vanishing_coefficients`, `affine_inconsistent_unit_coefficients`,
`affineLinearPart_injOn_proper`, `affine_independent_linearParts`,
`affine_proper_linearPart_finrank`, `affine_proper_nonzero_degree_one`).
Theorem statements keep his quantifier shape; names are prefixed `bAff` where they would clash.

An affine form on `Fin n` is a coefficient vector indexed by `Option (Fin n)` (`none` is the
constant term).

LOG: R4 BraunAffineForm module (Phase 2.1 layer 1a)
-/

namespace SATurday.ProofComplexity.BraunLA

noncomputable section

open scoped BigOperators

/-- Coefficient vector of an affine form on `Fin n`; `none` is the constant term. -/
abbrev AffineForm (K : Type*) (n : ℕ) := Option (Fin n) → K

variable {K : Type*} [Field K] {n : ℕ}

/-- The basis form for a coefficient slot. -/
def affineUnit (i : Option (Fin n)) : AffineForm K n := fun j => if i = j then 1 else 0

/-- Value of the form at a point. -/
def affineValue (a : AffineForm K n) (x : Fin n → K) : K :=
  a none + ∑ i, a (some i) * x i

/-- Evaluation at a point, as a linear functional on forms. -/
def affineEvaluation (x : Fin n → K) : AffineForm K n →ₗ[K] K where
  toFun a := affineValue a x
  map_add' a b := by
    simp [affineValue, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    simp [affineValue, mul_add, Finset.mul_sum, mul_assoc]

/-- Drop the constant term. -/
def affineLinearPart : AffineForm K n →ₗ[K] (Fin n → K) where
  toFun a i := a (some i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ordinary polynomial with the given affine coefficients. -/
def affinePolynomial : AffineForm K n →ₗ[K] MvPolynomial (Fin n) K where
  toFun a := MvPolynomial.C (a none) + ∑ i, a (some i) • MvPolynomial.X i
  map_add' a b := by
    simp [map_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c a := by
    simp [smul_add, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, map_mul, mul_assoc]

theorem affinePolynomial_eval (a : AffineForm K n) (x : Fin n → K) :
    MvPolynomial.eval x (affinePolynomial a) = affineValue a x := by
  simp [affinePolynomial, affineValue, MvPolynomial.smul_eq_C_mul]

theorem affinePolynomial_degree (a : AffineForm K n) :
    (affinePolynomial a).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (by simp)

theorem affineValue_ext {a b : AffineForm K n}
    (h : ∀ x, affineValue a x = affineValue b x) : a = b := by
  have h0 : a none = b none := by simpa [affineValue] using h (fun _ => 0)
  funext i
  cases i with
  | none => exact h0
  | some j =>
    have hj := h (fun i => if j = i then 1 else 0)
    simp [affineValue, mul_ite, h0] at hj
    exact hj

theorem affinePolynomial_injective :
    Function.Injective (affinePolynomial (K := K) (n := n)) := by
  intro a b h
  apply affineValue_ext
  intro x
  rw [← affinePolynomial_eval, ← affinePolynomial_eval, h]

/-- The coefficient form of an affine map on `Fin n → K`. -/
def affineFormOfMap (f : (Fin n → K) →ᵃ[K] K) : AffineForm K n
  | none => f 0
  | some j => f.linear (fun i => if j = i then 1 else 0)

theorem affineFormOfMap_value (f : (Fin n → K) →ᵃ[K] K) (x : Fin n → K) :
    affineValue (affineFormOfMap f) x = f x := by
  have h := congrFun f.decomp x
  change f x = f.linear x + f 0 at h
  rw [LinearMap.pi_apply_eq_sum_univ f.linear x] at h
  simpa [affineValue, affineFormOfMap, smul_eq_mul, add_comm, mul_comm] using h.symm

theorem affineFormOfMap_polynomial_eval (f : (Fin n → K) →ᵃ[K] K) (x : Fin n → K) :
    MvPolynomial.eval x (affinePolynomial (affineFormOfMap f)) = f x := by
  rw [affinePolynomial_eval, affineFormOfMap_value]

theorem affinePolynomial_unit :
    affinePolynomial (affineUnit none : AffineForm K n) = 1 := by
  simp [affinePolynomial, affineUnit]

/-! ### Linear algebra of affine systems -/

private theorem dual_expansion (L : AffineForm K n →ₗ[K] K) (a : AffineForm K n) :
    L a = a none * L (affineUnit none) + ∑ i, a (some i) * L (affineUnit (some i)) := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [Fintype.sum_option, smul_eq_mul]
  rfl

private theorem value_normalize (L : AffineForm K n →ₗ[K] K)
    (ht : L (affineUnit none) ≠ 0) (a : AffineForm K n) :
    affineValue a (fun i => L (affineUnit (some i)) / L (affineUnit none)) =
      L a / L (affineUnit none) := by
  rw [dual_expansion L a]
  simp only [affineValue, div_eq_mul_inv, add_mul, Finset.sum_mul, mul_assoc,
    mul_inv_cancel₀ ht, mul_one]

private theorem value_shift (L : AffineForm K n →ₗ[K] K) (x : Fin n → K) (a : AffineForm K n) :
    affineValue a (fun i => L (affineUnit (some i)) + (1 - L (affineUnit none)) * x i) =
      L a + (1 - L (affineUnit none)) * affineValue a x := by
  rw [dual_expansion L a]
  simp only [affineValue, mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, a (some i) * ((1 - L (affineUnit none)) * x i)) =
    (1 - L (affineUnit none)) * ∑ i, a (some i) * x i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
  ring

/-- A subspace missing the constant form has a common zero. -/
theorem affine_proper_common_zero (S : Submodule K (AffineForm K n))
    (hS : affineUnit none ∉ S) :
    ∃ x : Fin n → K, ∀ a ∈ S, affineValue a x = 0 := by
  have hnot : ¬ ∀ L : Module.Dual K (AffineForm K n),
      L ∈ S.dualAnnihilator → L (affineUnit none) = 0 := fun h =>
    hS ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp h)
  push Not at hnot
  obtain ⟨L, hL, ht⟩ := hnot
  refine ⟨fun i => L (affineUnit (some i)) / L (affineUnit none), fun a ha => ?_⟩
  rw [value_normalize L ht, ((S.mem_dualAnnihilator L).mp hL) a ha, zero_div]

/-- A form vanishing on the common zero flat of a consistent subspace lies in it. -/
theorem affine_vanishing_mem_span (S : Submodule K (AffineForm K n))
    (x : Fin n → K) (hx : ∀ a ∈ S, affineValue a x = 0) (f : AffineForm K n)
    (hf : ∀ y : Fin n → K, (∀ a ∈ S, affineValue a y = 0) → affineValue f y = 0) :
    f ∈ S := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S f).mp
  intro L hL
  have hy : ∀ a ∈ S, affineValue a (fun i => L (affineUnit (some i)) +
      (1 - L (affineUnit none)) * x i) = 0 := by
    intro a ha
    rw [value_shift, ((S.mem_dualAnnihilator L).mp hL) a ha, hx a ha]
    simp
  have hh := hf _ hy
  rw [value_shift, hf x hx] at hh
  simpa using hh

private theorem span_zero {ι : Type*} (g : ι → AffineForm K n) (x : Fin n → K)
    (hx : ∀ i, affineValue (g i) x = 0) :
    ∀ a ∈ Submodule.span K (Set.range g), affineValue a x = 0 := by
  have hle : Submodule.span K (Set.range g) ≤ (affineEvaluation x).ker :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  exact fun a ha => hle ha

theorem affine_vanishing_coefficients {ι : Type*} [Fintype ι]
    (g : ι → AffineForm K n) (x : Fin n → K)
    (hx : ∀ i, affineValue (g i) x = 0) (f : AffineForm K n)
    (hf : ∀ y, (∀ i, affineValue (g i) y = 0) → affineValue f y = 0) :
    ∃ c : ι → K, f = ∑ i, c i • g i := by
  have hm := affine_vanishing_mem_span (Submodule.span K (Set.range g)) x
    (span_zero g x hx) f (fun y hy => hf y fun i => hy _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
  exact ⟨c, hc.symm⟩

theorem affine_inconsistent_unit_coefficients {ι : Type*} [Fintype ι]
    (g : ι → AffineForm K n) (h : ¬ ∃ x, ∀ i, affineValue (g i) x = 0) :
    ∃ c : ι → K, affineUnit none = ∑ i, c i • g i := by
  have hm : affineUnit none ∈ Submodule.span K (Set.range g) := by
    by_contra hn
    obtain ⟨x, hx⟩ := affine_proper_common_zero _ hn
    exact h ⟨x, fun i => hx _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
  exact ⟨c, hc.symm⟩

theorem affineLinearPart_injOn_proper (S : Submodule K (AffineForm K n))
    (hS : affineUnit none ∉ S) : Set.InjOn affineLinearPart (S : Set (AffineForm K n)) := by
  obtain ⟨x, hx⟩ := affine_proper_common_zero S hS
  intro a ha b hb hab
  have hlin : ∀ i, a (some i) = b (some i) := fun i => congrFun hab i
  have hconst : a none = b none := by
    have hA := hx a ha
    have hB := hx b hb
    simp only [affineValue, hlin] at hA hB
    exact add_right_cancel (hA.trans hB.symm)
  funext i
  cases i with
  | none => exact hconst
  | some i => exact hlin i

theorem affine_independent_linearParts {ι : Type*} (g : ι → AffineForm K n)
    (hg : LinearIndependent K g)
    (hproper : affineUnit none ∉ Submodule.span K (Set.range g)) :
    LinearIndependent K (fun i => affineLinearPart (g i)) :=
  hg.map_injOn affineLinearPart (affineLinearPart_injOn_proper _ hproper)

theorem affine_proper_linearPart_finrank (S : Submodule K (AffineForm K n))
    (hS : affineUnit none ∉ S) :
    Module.finrank K (S.map affineLinearPart) = Module.finrank K S := by
  have hi : Function.Injective (affineLinearPart.comp S.subtype) := fun a b h =>
    Subtype.ext (affineLinearPart_injOn_proper S hS a.property b.property h)
  have he : (affineLinearPart.comp S.subtype).range = S.map affineLinearPart := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj hi

theorem affine_proper_nonzero_degree_one (S : Submodule K (AffineForm K n))
    (hS : affineUnit none ∉ S) (a : AffineForm K n) (ha : a ∈ S) (hne : a ≠ 0) :
    (affinePolynomial a).totalDegree = 1 := by
  have hd := affinePolynomial_degree a
  have hz : (affinePolynomial a).totalDegree ≠ 0 := by
    intro hz
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
    obtain ⟨x, hx⟩ := affine_proper_common_zero S hS
    have hev := congrArg (MvPolynomial.eval x) hc
    rw [affinePolynomial_eval, hx a ha, MvPolynomial.eval_C] at hev
    rw [← hev, map_zero] at hc
    exact hne (affinePolynomial_injective (hc.trans (map_zero affinePolynomial).symm))
  omega

end

end SATurday.ProofComplexity.BraunLA
