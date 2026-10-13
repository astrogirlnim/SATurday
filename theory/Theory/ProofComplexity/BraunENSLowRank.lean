import Theory.ProofComplexity.BraunENS
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Scalar cleanup and low rank ENS specialization (R4 Phase 2.1, layer 3b)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`FreshENSScalarCleanup.lean` (`freshENS_scalar_cleanup`, `freshENS_zero_cleanup`,
`freshENS_unit_cleanup`, `freshENS_unitSpan_cleanup`: degree preserving ordinary PC deletion of
zero and binary unit span fresh blocks) and `LowRankENS.lean` (`lowBinCoefficients_degree`,
`lowRankENS_specialization`: no retained core packing of an affine input span into bounded bins,
exact zero indicator product, degree bounded coefficients, ordinary Boolean NS companions).
Statements keep his quantifier shape; they sit on `BraunPC`, `BraunPCBoolean`, `BraunENS`.

LOG: R4 BraunENSLowRank module (Phase 2.1 layer 3b)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators

section Cleanup
variable {K σ ι : Type*} [Field K] [Fintype ι] {h : ℕ}

def freshENSBlockAxioms (g : ι → MvPolynomial σ K) (h : ℕ) :
    Set (MvPolynomial (FreshENSVars σ ι h) K) :=
  {p | ∃ i, p = freshENSCompanion g h i} ∪
  {p | ∃ u : Fin h, ∃ i : ι, p = X (Sum.inr (u, i)) ^ 2 - X (Sum.inr (u, i))}

def freshENSScalarVars (c : Fin h × ι → K) : FreshENSVars σ ι h → MvPolynomial σ K
  | Sum.inl x => X x
  | Sum.inr v => C (c v)

def freshENSScalar (c : Fin h × ι → K) :
    MvPolynomial (FreshENSVars σ ι h) K →ₐ[K] MvPolynomial σ K := aeval (freshENSScalarVars c)

omit [Fintype ι] in
theorem freshENSScalar_old (c : Fin h × ι → K) (p : MvPolynomial σ K) :
    freshENSScalar c (rename Sum.inl p) = p := by
  rw [freshENSScalar, aeval_rename]
  change aeval X p = p
  exact aeval_X_left_apply p

omit [Fintype ι] in
private theorem scalar_degree (c : Fin h × ι → K) (p : MvPolynomial (FreshENSVars σ ι h) K) :
    (freshENSScalar c p).totalDegree ≤ p.totalDegree := by
  have hc : ∀ v, (freshENSScalarVars (σ := σ) c v).totalDegree ≤ 1 := by
    intro v; cases v <;> simp [freshENSScalarVars]
  simpa [freshENSScalar] using substitution_degree (freshENSScalarVars c) 1 hc p

theorem freshENS_scalar_cleanup (g : ι → MvPolynomial σ K) (h : ℕ)
    (F : Set (MvPolynomial σ K)) (c : Fin h × ι → K)
    (hc : ∀ v, c v ^ 2 = c v)
    (hcomp : ∀ i, freshENSScalar c (freshENSCompanion g h i) = 0)
    {D : ℕ} {p : MvPolynomial (FreshENSVars σ ι h) K}
    (hp : Derives ((rename Sum.inl) '' F ∪ freshENSBlockAxioms g h) D p) :
    Derives F D (freshENSScalar c p) := by
  have hvars : ∀ v, (freshENSScalarVars (σ := σ) c v).totalDegree ≤ 1 := by
    intro v; cases v <;> simp [freshENSScalarVars]
  have hh := hp.substitute_weighted (freshENSScalarVars c) 1 hvars F 1 (by
    intro a ha hd
    simp only [totalDegree_one, Nat.add_zero, one_mul]
    change Derives F D (freshENSScalar c a)
    rcases ha with ha | ha
    · obtain ⟨q, hq, rfl⟩ := ha
      have hdeg := (scalar_degree c (rename Sum.inl q)).trans hd
      rw [freshENSScalar_old] at hdeg ⊢
      exact .hyp hq hdeg
    · rcases ha with ⟨i, rfl⟩ | ⟨u, i, rfl⟩
      · rw [hcomp]; exact .zero
      · have hz : freshENSScalar (σ := σ) c
            (X (Sum.inr (u, i)) ^ 2 - X (Sum.inr (u, i))) = 0 := by
          simp only [freshENSScalar, map_sub, map_pow, aeval_X, freshENSScalarVars]
          rw [← map_pow, hc, sub_self]
        rw [hz]; exact .zero)
  simpa [freshENSScalar] using hh

theorem freshENS_zero_cleanup (g : ι → MvPolynomial σ K) (h : ℕ)
    (hg : ∀ i, g i = 0) (F : Set (MvPolynomial σ K))
    {D : ℕ} {p : MvPolynomial (FreshENSVars σ ι h) K}
    (hp : Derives ((rename Sum.inl) '' F ∪ freshENSBlockAxioms g h) D p) :
    Derives F D (freshENSScalar (fun _ => 0) p) := by
  apply freshENS_scalar_cleanup g h F (fun _ => 0) (by simp)
  · intro i
    simp [freshENSCompanion, hg]
  · exact hp

def freshENSUnitScalars {h : ℕ} (c : ι → K) : Fin h × ι → K :=
  fun v => if v.1.val = 0 then c v.2 else 0

private theorem unitScalar_product (g : ι → MvPolynomial σ K) (h : ℕ)
    (hh : 0 < h) (c : ι → K) (hc : ∑ i, c i • g i = 1) :
    freshENSScalar (freshENSUnitScalars c) (freshENSProduct g h) = 0 := by
  classical
  rw [freshENSProduct, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hh⟩ : Fin h))
  simp only [freshENSFactor, map_sub, map_one, map_sum, map_mul, freshENSScalar_old]
  simp only [freshENSScalar, aeval_X, freshENSScalarVars]
  simpa [freshENSUnitScalars, ← MvPolynomial.smul_eq_C_mul] using sub_eq_zero.mpr hc.symm

theorem freshENS_unit_cleanup (g : ι → MvPolynomial σ (ZMod 2)) (h : ℕ)
    (hh : 0 < h) (c : ι → ZMod 2) (hc : ∑ i, c i • g i = 1)
    (F : Set (MvPolynomial σ (ZMod 2)))
    {D : ℕ} {p : MvPolynomial (FreshENSVars σ ι h) (ZMod 2)}
    (hp : Derives ((rename Sum.inl) '' F ∪ freshENSBlockAxioms g h) D p) :
    Derives F D (freshENSScalar (freshENSUnitScalars c) p) := by
  apply freshENS_scalar_cleanup g h F (freshENSUnitScalars c)
  · intro v
    exact ZMod.pow_card _
  · intro i
    rw [freshENSCompanion, map_mul, unitScalar_product g h hh c hc, mul_zero]
  · exact hp

theorem freshENS_unitSpan_cleanup (g : ι → MvPolynomial σ (ZMod 2)) (h : ℕ)
    (hh : 0 < h) (hunit : (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range g))
    (F : Set (MvPolynomial σ (ZMod 2)))
    {D : ℕ} {p : MvPolynomial (FreshENSVars σ ι h) (ZMod 2)}
    (hp : Derives ((rename Sum.inl) '' F ∪ freshENSBlockAxioms g h) D p) :
    ∃ c : ι → ZMod 2, Derives F D (freshENSScalar (freshENSUnitScalars c) p) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hunit
  exact ⟨c, freshENS_unit_cleanup g h hh c hc F hp⟩


end Cleanup

section LowRank

private def binEmbedding {r h k : ℕ} (hr : r ≤ h * (k + 1)) :
    Fin r ↪ Fin h × Fin (k + 1) :=
  (Fin.castLEEmb hr).trans finProdFinEquiv.symm.toEmbedding

private def ensBin {r h k : ℕ} (e : Fin r ↪ Fin h × Fin (k + 1)) (u : Fin h) : Finset (Fin r) :=
  Finset.univ.filter (fun j => (e j).1 = u)

private theorem ensBin_card {r h k : ℕ} (e : Fin r ↪ Fin h × Fin (k + 1)) (u : Fin h) :
    (ensBin e u).card ≤ k + 1 := by
  let f : (ensBin e u) → Fin (k + 1) := fun j => (e j.val).2
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact (Finset.mem_filter.mp a.property).2.trans (Finset.mem_filter.mp b.property).2.symm
    · exact hab
  simpa using Fintype.card_le_of_injective f hi

private def lowPrefix {σ : Type} {r h k : ℕ}
    (F : Fin r → MvPolynomial σ (ZMod 2))
    (e : Fin r ↪ Fin h × Fin (k + 1)) (u : Fin h) (j : Fin r) :
    MvPolynomial σ (ZMod 2) := ∏ t ∈ (ensBin e u).filter (fun t => t < j), (1 - F t)

private theorem lowPrefix_degree {σ : Type} {r h k : ℕ}
    (F : Fin r → MvPolynomial σ (ZMod 2)) (hF : ∀ j, (F j).totalDegree ≤ 1)
    (e : Fin r ↪ Fin h × Fin (k + 1)) (u : Fin h) (j : Fin r) (hj : j ∈ ensBin e u) :
    (lowPrefix F e u j).totalDegree ≤ k := by
  have hc : ((ensBin e u).filter (fun t => t < j)).card < (ensBin e u).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have := heq.symm ▸ hj
    simp at this
  have hsize := ensBin_card e u
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _t ∈ (ensBin e u).filter (fun t => t < j), 1 := by
      apply Finset.sum_le_sum
      intro t _
      exact (totalDegree_sub _ _).trans (max_le (by simp) (hF t))
    _ ≤ k := by simp only [Finset.sum_const, smul_eq_mul, mul_one]; omega

def lowBinCoefficients {σ ι : Type} [Fintype ι] {r h k : ℕ}
    (F : Fin r → MvPolynomial σ (ZMod 2)) (c : Fin r → ι → ZMod 2)
    (e : Fin r ↪ Fin h × Fin (k + 1)) (v : Fin h × ι) :
    MvPolynomial σ (ZMod 2) := ∑ j ∈ ensBin e v.1, c j v.2 • lowPrefix F e v.1 j

theorem lowBinCoefficients_degree {σ ι : Type} [Fintype ι] {r h k : ℕ}
    (F : Fin r → MvPolynomial σ (ZMod 2)) (hF : ∀ j, (F j).totalDegree ≤ 1)
    (c : Fin r → ι → ZMod 2) (e : Fin r ↪ Fin h × Fin (k + 1)) (v : Fin h × ι) :
    (lowBinCoefficients F c e v).totalDegree ≤ k := by
  apply totalDegree_finsetSum_le
  intro j hj
  exact (totalDegree_smul_le _ _).trans (lowPrefix_degree F hF e v.1 j hj)

private theorem lowBin_identity {σ ι : Type} [Fintype ι] {r h k : ℕ}
    (g : ι → MvPolynomial σ (ZMod 2)) (F : Fin r → MvPolynomial σ (ZMod 2))
    (c : Fin r → ι → ZMod 2) (hc : ∀ j, ∑ i, c j i • g i = F j)
    (e : Fin r ↪ Fin h × Fin (k + 1)) (u : Fin h) :
    1 - ∑ i, lowBinCoefficients F c e (u, i) * g i =
      ∏ j ∈ ensBin e u, (1 - F j) := by
  rw [Finset.prod_one_sub_ordered]
  congr 1
  simp only [lowBinCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ i, (c j i • lowPrefix F e u j) * g i) = F j * lowPrefix F e u j
  calc
    _ = ∑ i, (c j i • g i) * lowPrefix F e u j := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [smul_eq_C_mul]
      ring
    _ = _ := by rw [← Finset.sum_mul, hc]

private theorem polynomialSubstitution_old {σ ι : Type} {h : ℕ}
    (β : Fin h × ι → MvPolynomial σ (ZMod 2)) (p : MvPolynomial σ (ZMod 2)) :
    aeval (Sum.elim X β) (rename Sum.inl p) = p := by
  rw [aeval_rename]
  exact aeval_X_left_apply p

private theorem lowBin_product {σ ι : Type} [Fintype ι] {r h k : ℕ}
    (g : ι → MvPolynomial σ (ZMod 2)) (F : Fin r → MvPolynomial σ (ZMod 2))
    (c : Fin r → ι → ZMod 2) (hc : ∀ j, ∑ i, c j i • g i = F j)
    (e : Fin r ↪ Fin h × Fin (k + 1)) :
    aeval (Sum.elim X (lowBinCoefficients F c e)) (freshENSProduct g h) =
      ∏ j : Fin r, (1 - F j) := by
  rw [freshENSProduct, map_prod]
  calc
    _ = ∏ u : Fin h, ∏ j ∈ ensBin e u, (1 - F j) := by
      apply Finset.prod_congr rfl
      intro u _
      simp only [freshENSFactor, map_sub, map_one, map_sum, map_mul, aeval_X,
        Sum.elim_inr, polynomialSubstitution_old]
      exact lowBin_identity g F c hc e u
    _ = _ := Finset.prod_fiberwise Finset.univ (fun j => (e j).1) (fun j => 1 - F j)

private theorem product_complements_degree {σ : Type} {r : ℕ}
    (F : Fin r → MvPolynomial σ (ZMod 2)) (hF : ∀ j, (F j).totalDegree ≤ 1) :
    (∏ j : Fin r, (1 - F j)).totalDegree ≤ r := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _j : Fin r, 1 := Finset.sum_le_sum (fun j _ =>
      (totalDegree_sub _ _).trans (max_le (by simp) (hF j)))
    _ = r := by simp

private theorem binary_nonzero_eq_one (v : ZMod 2) (hv : v ≠ 0) : v = 1 := by
  fin_cases v
  · exact (hv rfl).elim
  · rfl

private theorem product_complements_indicator {σ : Type} {r : ℕ}
    (F : Fin r → MvPolynomial σ (ZMod 2)) (x : σ → ZMod 2) :
    eval x (∏ j : Fin r, (1 - F j)) = if ∀ j, eval x (F j) = 0 then 1 else 0 := by
  classical
  by_cases hx : ∀ j, eval x (F j) = 0
  · simp [hx]
  · rw [if_neg hx, map_prod]
    push Not at hx
    obtain ⟨j, hj⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [binary_nonzero_eq_one _ hj]

private theorem lowRank_of_spanning_family {σ ι : Type} [Fintype σ] [Fintype ι]
    {r h k : ℕ} (g : ι → MvPolynomial σ (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1)
    (F : Fin r → MvPolynomial σ (ZMod 2)) (hF : ∀ j, (F j).totalDegree ≤ 1)
    (c : Fin r → ι → ZMod 2) (hc : ∀ j, ∑ i, c j i • g i = F j)
    (d : ι → Fin r → ZMod 2) (hd : ∀ i, ∑ j, d i j • F j = g i)
    (hr : r ≤ h * (k + 1)) :
    ∃ (β : Fin h × ι → MvPolynomial σ (ZMod 2)) (Z : MvPolynomial σ (ZMod 2)),
      (∀ v, (β v).totalDegree ≤ k) ∧
      aeval (Sum.elim X β) (freshENSProduct g h) = Z ∧ Z.totalDegree ≤ r ∧
      (∀ x, eval x Z = if ∀ i, eval x (g i) = 0 then 1 else 0) ∧
      (∀ i, g i * Z ∈ nsSpace booleanBase (r + 1)) := by
  classical
  let e := binEmbedding hr
  let Z := ∏ j : Fin r, (1 - F j)
  have hzero (x : σ → ZMod 2) : (∀ j, eval x (F j) = 0) ↔ ∀ i, eval x (g i) = 0 := by
    constructor
    · intro hx i
      rw [← hd i]
      simp [smul_eval, hx]
    · intro hx j
      rw [← hc j]
      simp [smul_eval, hx]
  refine ⟨lowBinCoefficients F c e, Z, lowBinCoefficients_degree F hF c e,
    lowBin_product g F c hc e, product_complements_degree F hF, ?_, ?_⟩
  · intro x
    change eval x (∏ j : Fin r, (1 - F j)) = _
    simp only [product_complements_indicator, hzero x]
  · intro i
    apply boolean_vanishing_ns_bound
    · exact (totalDegree_mul _ _).trans (by
        have hh : Z.totalDegree ≤ r := product_complements_degree F hF
        have hi := hg i
        change (g i).totalDegree + Z.totalDegree ≤ r + 1
        omega)
    · intro x
      rw [map_mul]
      change eval x (g i) * eval x (∏ j : Fin r, (1 - F j)) = 0
      simp only [product_complements_indicator, hzero x]
      split_ifs with hx
      · simp [hx i]
      · simp

theorem lowRankENS_specialization {σ ι : Type} [Fintype σ] [Fintype ι]
    (g : ι → MvPolynomial σ (ZMod 2)) (hg : ∀ i, (g i).totalDegree ≤ 1) (h k : ℕ)
    (hr : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1)) :
    ∃ (β : Fin h × ι → MvPolynomial σ (ZMod 2)) (Z : MvPolynomial σ (ZMod 2)),
      (∀ v, (β v).totalDegree ≤ k) ∧
      aeval (Sum.elim X β) (freshENSProduct g h) = Z ∧
      Z.totalDegree ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ∧
      (∀ x, eval x Z = if ∀ i, eval x (g i) = 0 then 1 else 0) ∧
      (∀ i, g i * Z ∈ nsSpace booleanBase
        (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) + 1)) := by
  classical
  let S := Submodule.span (ZMod 2) (Set.range g)
  let _ : FiniteDimensional (ZMod 2) S := FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range g)
  let B := Module.finBasis (ZMod 2) S
  let A := fun j => (B j).val
  have hS : S ≤ degreeSpace 1 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hg i
  have hA : ∀ j, (A j).totalDegree ≤ 1 := fun j => hS (B j).property
  have hc : ∀ j, ∃ c : ι → ZMod 2, ∑ i, c i • g i = A j := by
    intro j
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp (B j).property
  choose c hc using hc
  have hd : ∀ i, ∃ d : Fin (Module.finrank (ZMod 2) S) → ZMod 2, ∑ j, d j • A j = g i := by
    intro i
    let v : S := ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩
    refine ⟨fun j => B.repr v j, ?_⟩
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using congrArg Subtype.val (B.sum_repr v)
  choose d hd using hd
  exact lowRank_of_spanning_family g hg A hA c hc d hd hr


end LowRank

end

end SATurday.ProofComplexity.BraunPC
