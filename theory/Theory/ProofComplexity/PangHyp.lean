import Theory.ProofComplexity.PangDescent
import Mathlib.RingTheory.Localization.Integer

/-!
# Pang route, layer B/C interface: polynomial-coefficient form of the Frobenius hypothesis

`AHm N` says: for every finitely supported family `u_α` of vectors (a vector of polynomials in `λ`),
if the pencil `∑ λ_i N_i` kills it coefficientwise, so does `∑ λ_i^p N_i`.  `hyp_of_AHm` shows this
implies the kernel inclusion `ker M(λ) ⊆ ker M(λ^p)` over `F_p(λ)` required by `pang_rank_retention`
(clearing denominators), so Lemma 2.3 (base change) is not needed.
-/

namespace Pang
open MvPolynomial

variable {p : ℕ} [Fact p.Prime] {s m k : ℕ}

/-- Coefficient `β` of `∑_i λ_i^e N_i u(λ)` where `u(λ) = ∑_α λ^α u_α`. -/
noncomputable def shiftSum {U W : Type*} [AddCommMonoid W] [Zero U] (e : ℕ) (N : Fin s → U → W)
    (u : (Fin s →₀ ℕ) → U) (β : Fin s →₀ ℕ) : W :=
  ∑ i, if e ≤ β i then N i (u (β - Finsupp.single i e)) else 0

/-- Matrix form of the Frobenius hypothesis, in polynomial coefficients. -/
def AHm (N : Fin s → Matrix (Fin m) (Fin k) (ZMod p)) : Prop :=
  ∀ u : (Fin s →₀ ℕ) → (Fin k → ZMod p), (Function.support u).Finite →
    (∀ β, shiftSum 1 (fun i x => (N i).mulVec x) u β = 0) →
    ∀ β, shiftSum p (fun i x => (N i).mulVec x) u β = 0

lemma coeff_X_pow_mul_aux (e : ℕ) (i : Fin s) (q : MvPolynomial (Fin s) (ZMod p))
    (β : Fin s →₀ ℕ) :
    coeff β (X i ^ e * q) = if e ≤ β i then coeff (β - Finsupp.single i e) q else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  simp only [one_mul, Finsupp.single_le_iff]

theorem hyp_of_AHm (N : Fin s → Matrix (Fin m) (Fin k) (ZMod p)) (h : AHm N) :
    ∀ u : Fin k → FRat p s,
      (pencilE (fun i => evFR p s (X i)) 1 ((evFR p s).comp C) N).mulVec u = 0 →
      (pencilE (fun i => evFR p s (X i)) p ((evFR p s).comp C) N).mulVec u = 0 := by
  classical
  intro u hu
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial (Fin s) (ZMod p))) u
  choose v hv using hb
  -- hv : algebraMap (v j) = b • u j
  let Eq' : ℕ → Fin m → MvPolynomial (Fin s) (ZMod p) := fun e r =>
    ∑ i, X i ^ e * ∑ j, C (N i r j) * v j
  have hmap : ∀ e r, evFR p s (Eq' e r) = (b : MvPolynomial (Fin s) (ZMod p)) •
      ((pencilE (fun i => evFR p s (X i)) e ((evFR p s).comp C) N).mulVec u r) := by
    intro e r
    simp only [Eq', map_sum, map_mul, map_pow, pencilE, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Finset.smul_sum, Finset.sum_mul, Finset.mul_sum, RingHom.comp_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have := hv j
    simp only [Algebra.smul_def] at this ⊢
    rw [show evFR p s (v j) = algebraMap _ _ (v j) from rfl, this]
    ring
  have hcoef : ∀ e r β, coeff β (Eq' e r) =
      shiftSum e (fun i x => (N i).mulVec x) (fun α j => coeff α (v j)) β r := by
    intro e r β
    simp only [Eq', shiftSum, coeff_sum, coeff_X_pow_mul_aux, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with he
    · simp [Matrix.mulVec, dotProduct, coeff_C_mul]
    · simp
  have hfin : (Function.support fun α j => coeff α (v j)).Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_univ (α := Fin k))
      (fun j _ => ((v j).support.finite_toSet))) ?_
    intro α hα
    simp only [Function.mem_support, ne_eq] at hα
    have : ∃ j, coeff α (v j) ≠ 0 := by
      by_contra hc
      exact hα (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
    obtain ⟨j, hj⟩ := this
    exact Set.mem_biUnion (Set.mem_univ j) (by simpa using hj)
  have hinj : Function.Injective (evFR p s) := IsFractionRing.injective _ _
  have h1 : ∀ β, shiftSum 1 (fun i x => (N i).mulVec x) (fun α j => coeff α (v j)) β = 0 := by
    intro β
    funext r
    rw [← hcoef]
    have : Eq' 1 r = 0 := by
      apply hinj
      rw [hmap, map_zero]
      have := congrFun hu r
      simp only [Pi.zero_apply] at this
      rw [this]; simp
    rw [this]; simp
  have h2 := h _ hfin h1
  funext r
  have hz : Eq' p r = 0 := by
    ext β
    rw [hcoef, h2 β]; simp
  have := hmap p r
  rw [hz, map_zero] at this
  have hb0 : (b : MvPolynomial (Fin s) (ZMod p)) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  rw [Algebra.smul_def] at this
  have hb1 : algebraMap (MvPolynomial (Fin s) (ZMod p)) (FRat p s) b ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hb0
  rcases mul_eq_zero.1 this.symm with h0 | h0
  · exact absurd h0 hb1
  · simpa using h0


section Lin
variable {U W : Type*} [AddCommGroup U] [Module (ZMod p) U] [AddCommGroup W] [Module (ZMod p) W]

/-- The Frobenius hypothesis for linear maps, in polynomial coefficients. -/
def AH (N : Fin s → U →ₗ[ZMod p] W) : Prop :=
  ∀ u : (Fin s →₀ ℕ) → U, (Function.support u).Finite →
    (∀ β, shiftSum 1 (fun i x => N i x) u β = 0) → ∀ β, shiftSum p (fun i x => N i x) u β = 0

lemma shiftSum_map {W₂ : Type*} [AddCommGroup W₂] (L : W →+ W₂) (f : Fin s → U → W) (e : ℕ)
    (u : (Fin s →₀ ℕ) → U) (β : Fin s →₀ ℕ) :
    shiftSum e (fun i x => L (f i x)) u β = L (shiftSum e f u β) := by
  unfold shiftSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma matrix_rank_eq {K : Type*} [Field K] {U W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U] {k : ℕ} {ι : Type*} [Fintype ι] (bU : Module.Basis (Fin k) K U) (f : U →ₗ[K] W)
    (A : Matrix ι (Fin k) K) (hA : ∀ x, A.mulVec (bU.equivFun x) = 0 ↔ f x = 0) :
    A.rank = Module.finrank K (LinearMap.range f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have hU : Module.finrank K U = k := by
    rw [Module.finrank_eq_card_basis bU]; simp
  have hk : Module.finrank K (Fin k → K) = k := by simp
  have hker : (LinearMap.ker f).map (bU.equivFun : U →ₗ[K] Fin k → K) = LinearMap.ker A.mulVecLin := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (hA x).2 hx
    · intro hy
      have e : bU.equivFun (bU.equivFun.symm y) = y := LinearEquiv.apply_symm_apply _ _
      refine ⟨bU.equivFun.symm y, ?_, e⟩
      exact (hA _).1 (by rw [e]; exact hy)
  have h3 := LinearEquiv.finrank_map_eq bU.equivFun (LinearMap.ker f)
  rw [hker] at h3
  unfold Matrix.rank
  omega


/-- **Rank retention for linear maps** (Pang Cor. 3.4 minus its hypothesis check): under the
Frobenius hypothesis `AH N` some `F_p`-combination loses at most a factor `1 - 1/p` of the rank of
the stacked map. -/
theorem pang_retention_lin [Module.Finite (ZMod p) U] (N : Fin s → U →ₗ[ZMod p] W) (hAH : AH N) :
    ∃ c : Fin s → ZMod p, Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi N)) * (p - 1) ≤
      p * Module.finrank (ZMod p) (LinearMap.range (∑ i, c i • N i)) := by
  classical
  set W' : Submodule (ZMod p) W := ⨆ i, LinearMap.range (N i) with hW'
  haveI : FiniteDimensional (ZMod p) W' := Submodule.finiteDimensional_iSup _
  have hmem : ∀ i x, N i x ∈ W' := fun i x => Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
  let N' : Fin s → U →ₗ[ZMod p] W' := fun i => (N i).codRestrict W' (hmem i)
  let bU := Module.finBasis (ZMod p) U
  let bW := Module.finBasis (ZMod p) W'
  let M : Fin s → Matrix (Fin (Module.finrank (ZMod p) W')) (Fin (Module.finrank (ZMod p) U))
      (ZMod p) := fun i => LinearMap.toMatrix bU bW (N' i)
  have hM : ∀ i x, (M i).mulVec (bU.equivFun x) = bW.equivFun (N' i x) := by
    intro i x
    have := LinearMap.toMatrix_mulVec_repr bU bW (N' i) x
    simpa using this
  have hsub : ∀ i x, N i x = (N' i x : W) := fun i x => rfl
  have hAHm : AHm M := by
    intro u hfin h1 β
    let uU : (Fin s →₀ ℕ) → U := fun α => bU.equivFun.symm (u α)
    have hfinU : (Function.support uU).Finite := by
      refine hfin.subset fun α hα => ?_
      simp only [Function.mem_support, ne_eq] at hα ⊢
      intro h0; apply hα; simp [uU, h0]
    have key : ∀ e γ, shiftSum e (fun i x => (M i).mulVec x) u γ =
        bW.equivFun (shiftSum e (fun i x => N' i x) uU γ) := by
      intro e γ
      have := shiftSum_map (U := U) (W := W') (bW.equivFun.toLinearMap.toAddMonoidHom)
        (fun i x => N' i x) e uU γ
      simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe] at this
      rw [← this]
      unfold shiftSum
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs
      · show (M i).mulVec (u _) = bW.equivFun (N' i (uU _))
        rw [← hM i (uU _)]
        simp only [uU, LinearEquiv.apply_symm_apply]
      · rfl
    have key2 : ∀ e γ, shiftSum e (fun i x => N i x) uU γ = ((shiftSum e (fun i x => N' i x) uU γ : W') : W) := by
      intro e γ
      have := shiftSum_map (U := U) (W := W') W'.subtype.toAddMonoidHom (fun i x => N' i x) e uU γ
      exact this
    have h1' : ∀ γ, shiftSum 1 (fun i x => N i x) uU γ = 0 := by
      intro γ
      have := h1 γ
      rw [key] at this
      have h0 : shiftSum 1 (fun i x => N' i x) uU γ = 0 := (map_eq_zero_iff _ bW.equivFun.injective).1 this
      rw [key2, h0]; rfl
    have h2 := hAH uU hfinU h1' β
    have : shiftSum p (fun i x => N' i x) uU β = 0 := by
      apply Subtype.ext
      rw [← key2]; simpa using h2
    rw [key, this, map_zero]
  obtain ⟨c, hc⟩ := pang_rank_retention M (hyp_of_AHm M hAHm)
  refine ⟨c, ?_⟩
  have hst : (stackM M).rank = Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi N)) := by
    refine matrix_rank_eq bU (LinearMap.pi N) (stackM M) fun x => ?_
    have hrow : ∀ i r, ((stackM M).mulVec (bU.equivFun x)) (i, r) = (bW.equivFun (N' i x)) r := by
      intro i r; rw [← hM]; rfl
    constructor
    · intro h
      funext i
      have : bW.equivFun (N' i x) = 0 := by
        funext r; rw [← hrow]; exact congrFun h (i, r)
      have h0 : N' i x = 0 := (map_eq_zero_iff _ bW.equivFun.injective).1 this
      simp [hsub, h0]
    · intro h
      funext ⟨i, r⟩
      have h0 : N i x = 0 := congrFun h i
      have : N' i x = 0 := Subtype.ext (by rw [← hsub]; simpa using h0)
      rw [hrow, this]; simp
  have hpen : (pencilAt M c).rank = Module.finrank (ZMod p) (LinearMap.range (∑ i, c i • N i)) := by
    refine matrix_rank_eq bU (∑ i, c i • N i) (pencilAt M c) fun x => ?_
    have e1 : (pencilAt M c).mulVec (bU.equivFun x) = bW.equivFun (∑ i, c i • N' i x) := by
      funext r
      simp only [pencilAt, Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrFun (hM i x) r
      simp only [Matrix.mulVec, dotProduct] at this
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have e2 : ((∑ i, c i • N i : U →ₗ[ZMod p] W) x) = ((∑ i, c i • N' i x : W') : W) := by
      simp [hsub]
    rw [e1, e2]
    constructor
    · intro h
      have h0 := (map_eq_zero_iff _ bW.equivFun.injective).1 h
      rw [h0]; rfl
    · intro h
      have : (∑ i, c i • N' i x : W') = 0 := Subtype.ext (by simpa using h)
      rw [this, map_zero]
  rw [hst, hpen] at hc
  exact hc

end Lin

end Pang
