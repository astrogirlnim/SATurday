import Theory.ProofComplexity.PangPencil
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
/-
# Pang route, layer C: Frobenius kernel descent (Pang Lemmas 3.2, 3.3)

`frob_descent`: a Frobenius-stable subspace `W` of `E^ι` (char p) contains `finrank W` vectors with
entries in `F_p` that are `F_p`-linearly independent (pivot-coordinate argument).
`pencil_descent_rank`: if `ker M(λ) ⊆ ker M(λ^p)` over a field `E` containing `F_p[λ]`, then
`rank_{F_p} (stack M_i) ≤ rank_E M(λ)`.  `pang_rank_retention` combines this with the rank
specialization `pencil_sum`: some `c ∈ F_p^s` has `rank (∑ c_i M_i) ≥ (1 - 1/p) rank (stack M_i)`.
-/
open Matrix
namespace Pang
variable {K : Type*} [Field K]

/-- A matrix has `rank A` linearly independent columns. -/
lemma exists_cols {ι ι' : Type*} [Fintype ι] [Fintype ι'] (A : Matrix ι' ι K) :
    ∃ c : Fin A.rank → ι, LinearIndependent K (A.submatrix id c).col := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    have h1 : Module.finrank K (Submodule.span K (Set.range (A.col ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card hli
    rw [hspan] at h1
    rw [← h1, Matrix.rank_eq_finrank_span_cols]
  let e : Fin A.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have : (A.submatrix id (a ∘ e)).col = (A.col ∘ a) ∘ e := by
    ext i j; simp [Matrix.col, Function.comp]
  rw [this]
  exact hli.comp e e.injective

lemma exists_cols' {ι ι' : Type*} [Fintype ι] [Fintype ι'] (A : Matrix ι' ι K) (n : ℕ)
    (hn : A.rank = n) : ∃ c : Fin n → ι, LinearIndependent K (A.submatrix id c).col := by
  subst hn; exact exists_cols A

/-- A matrix of rank `R` has a nonvanishing `R × R` minor. -/
lemma exists_minor {m k : ℕ} (A : Matrix (Fin m) (Fin k) K) :
    ∃ (r : Fin A.rank → Fin m) (c : Fin A.rank → Fin k), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_cols A
  have hBrank : (A.submatrix id c).rank = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hc]; simp
  have hBt : (A.submatrix id c)ᵀ.rank = A.rank := by rw [Matrix.rank_transpose, hBrank]
  obtain ⟨r, hr⟩ := exists_cols' (A.submatrix id c)ᵀ A.rank hBt
  refine ⟨r, c, ?_⟩
  have hS : LinearIndependent K ((A.submatrix id c).submatrix r id).row := by
    have : ((A.submatrix id c)ᵀ.submatrix id r).col = ((A.submatrix id c).submatrix r id).row := by
      ext i j; simp [Matrix.col, Matrix.row]
    rw [← this]; exact hr
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hS
  have := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h2 : A.submatrix r c = (A.submatrix id c).submatrix r id := by ext i j; simp
  rw [h2]
  exact (isUnit_iff_ne_zero.1 this)

lemma le_rank_of_minor {m k R : ℕ} (A : Matrix (Fin m) (Fin k) K) (r : Fin R → Fin m)
    (c : Fin R → Fin k) (h : (A.submatrix r c).det ≠ 0) : R ≤ A.rank := by
  have hu : IsUnit (A.submatrix r c) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 : (A.submatrix r c).rank = R := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  rw [← h1]
  exact Matrix.rank_submatrix_le _ _ _

lemma rank_le_rank_map {L : Type*} [Field L] (f : K →+* L) {m k : ℕ} (A : Matrix (Fin m) (Fin k) K) :
    A.rank ≤ (A.map f).rank := by
  obtain ⟨r, c, h⟩ := exists_minor A
  apply le_rank_of_minor _ r c
  have : (A.map f).submatrix r c = (A.submatrix r c).map f := by ext i j; simp
  rw [this]
  have e := f.map_det (A.submatrix r c)
  rw [RingHom.mapMatrix_apply] at e
  rw [← e]
  exact (map_ne_zero f).2 h

open Polynomial in
lemma exists_algebraMap_of_pow_eq {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (x : E) (hx : x ^ p = x) : ∃ y : ZMod p, algebraMap (ZMod p) E y = x := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set P : E[X] := X ^ p - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hp
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq E hp
  have hsub : (Finset.univ.image (algebraMap (ZMod p) E)) ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, IsRoot, ← map_pow, ZMod.pow_card]
  have hcard1 : (Finset.univ.image (algebraMap (ZMod p) E)).card = p := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) E).injective]; simp
  have hcard2 : P.roots.toFinset.card ≤ p := by
    calc _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hxm : x ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, IsRoot, hx]
  rw [← heq] at hxm
  obtain ⟨y, _, hy⟩ := Finset.mem_image.1 hxm
  exact ⟨y, hy⟩

lemma frob_descent {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Submodule E (ι → E))
    (hW : ∀ w ∈ W, (fun i => w i ^ p) ∈ W) :
    ∃ b : Fin (Module.finrank E W) → ι → ZMod p, LinearIndependent (ZMod p) b ∧
      ∀ l, (fun i => algebraMap (ZMod p) E (b l i)) ∈ W := by
  set r := Module.finrank E W with hr
  let bW : Module.Basis (Fin r) E W := Module.finBasis E W
  let T : Matrix (Fin r) ι E := Matrix.of fun l i => (bW l : ι → E) i
  have hrows : LinearIndependent E T.row := by
    have := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    exact this
  have hrank : T.rank = r := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hrows]; simp
  obtain ⟨J, hJ⟩ := exists_cols' T r hrank
  set S : Matrix (Fin r) (Fin r) E := T.submatrix id J with hSdef
  have hS : IsUnit S := Matrix.linearIndependent_cols_iff_isUnit.1 hJ
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).1 hS
  set T' : Matrix (Fin r) ι E := S⁻¹ * T with hT'
  let t : Fin r → ι → E := fun j => T' j
  -- (a)
  have ha : ∀ j, t j ∈ W := by
    intro j
    have : t j = ((∑ l, S⁻¹ j l • bW l : W) : ι → E) := by
      ext i
      simp [t, hT', Matrix.mul_apply, T, Submodule.coe_sum, Finset.sum_apply]
    rw [this]; exact Submodule.coe_mem _
  -- (b)
  have hb : ∀ j n, t j (J n) = if j = n then 1 else 0 := by
    intro j n
    have : T' j (J n) = (S⁻¹ * S) j n := by
      simp [hT', Matrix.mul_apply, hSdef]
    rw [show t j (J n) = T' j (J n) from rfl, this, Matrix.nonsing_inv_mul _ hSdet]
    simp [Matrix.one_apply]
  -- (c)
  have hc : ∀ w ∈ W, ∀ i, w i = ∑ m, w (J m) * t m i := by
    intro w hw i
    set c := bW.repr ⟨w, hw⟩ with hcdef
    have h1 : ∀ x, w x = ∑ l, c l * T l x := by
      intro x
      have h0 : w = ∑ l, c l • (bW l : ι → E) := by
        refine (congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)).symm.trans ?_
        rw [Submodule.coe_sum]
        simp [hcdef]
      conv_lhs => rw [h0]
      simp [T, Finset.sum_apply]
    have hTS : ∀ l x, T l x = ∑ m, S l m * t m x := by
      intro l x
      have : (S * T') l x = T l x := by
        rw [hT', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSdet, Matrix.one_mul]
      rw [← this, Matrix.mul_apply]
    have h2 : ∀ x, w x = ∑ m, (∑ l, c l * S l m) * t m x := by
      intro x
      rw [h1 x]
      simp_rw [hTS, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    have h3 : ∀ n, w (J n) = ∑ l, c l * S l n := by
      intro n
      rw [h2 (J n)]
      simp [hb]
    rw [h2 i]
    exact Finset.sum_congr rfl fun m _ => by rw [h3 m]
  -- (d)
  have hd : ∀ j i, t j i ^ p = t j i := by
    intro j i
    have hw : (fun i => t j i ^ p) ∈ W := hW _ (ha j)
    have := hc _ hw i
    simp only [hb] at this
    have e : ∀ m : Fin r, (if j = m then (1 : E) else 0) ^ p = if j = m then 1 else 0 := by
      intro m
      split_ifs
      · simp
      · exact zero_pow (Fact.out : p.Prime).ne_zero
    simp only [e] at this
    simpa using this
  have hy : ∀ j i, ∃ y : ZMod p, algebraMap (ZMod p) E y = t j i :=
    fun j i => exists_algebraMap_of_pow_eq _ (hd j i)
  choose b hb' using hy
  refine ⟨b, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg n
    have h1 := congrFun hg (J n)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 : ∀ j, b j (J n) = if j = n then 1 else 0 := by
      intro j
      apply (algebraMap (ZMod p) E).injective
      rw [hb', hb]
      split_ifs <;> simp
    simp only [h2] at h1
    simpa using h1
  · intro j
    have : (fun i => algebraMap (ZMod p) E (b j i)) = t j := funext fun i => hb' j i
    rw [this]; exact ha j

section Descent
open MvPolynomial

variable {p : ℕ} [Fact p.Prime] {s m k : ℕ}

/-- Pencil over `E` with coefficients in `F_p`: `∑ λ_i^e N_i`. -/
def pencilE {E : Type*} [Field E] (lam : Fin s → E) (e : ℕ) (ev : ZMod p →+* E)
    (N : Fin s → Matrix (Fin m) (Fin k) (ZMod p)) : Matrix (Fin m) (Fin k) E :=
  Matrix.of fun u v => ∑ i, lam i ^ e * ev (N i u v)

/-- stacked matrix -/
def stackM (N : Fin s → Matrix (Fin m) (Fin k) (ZMod p)) : Matrix (Fin s × Fin m) (Fin k) (ZMod p) :=
  Matrix.of fun x v => N x.1 x.2 v

theorem pencil_descent_rank {E : Type*} [Field E] (evP : MvPolynomial (Fin s) (ZMod p) →+* E)
    (hev : Function.Injective evP)
    (N : Fin s → Matrix (Fin m) (Fin k) (ZMod p))
    (hyp : ∀ u : Fin k → E,
      (pencilE (fun i => evP (X i)) 1 (evP.comp C) N).mulVec u = 0 →
      (pencilE (fun i => evP (X i)) p (evP.comp C) N).mulVec u = 0) :
    (stackM N).rank ≤ (pencilE (fun i => evP (X i)) 1 (evP.comp C) N).rank := by
  classical
  haveI hchar : CharP E p :=
    charP_of_injective_ringHom (f := (evP.comp C : ZMod p →+* E)) (evP.comp C).injective p
  letI : Algebra (ZMod p) E := (evP.comp C).toAlgebra
  set lam : Fin s → E := fun i => evP (X i) with hlam
  set A : Matrix (Fin m) (Fin k) E := pencilE lam 1 (evP.comp C) N with hA
  set Ap : Matrix (Fin m) (Fin k) E := pencilE lam p (evP.comp C) N with hAp
  -- Ap is the Frobenius image of A
  have hfrob : Ap = A.map (frobenius E p) := by
    ext u v
    simp only [hAp, hA, pencilE, Matrix.of_apply, Matrix.map_apply, frobenius_def, pow_one]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ((evP.comp C) (N i u v)) ^ p = (evP.comp C) (N i u v) := by
      rw [← map_pow, ZMod.pow_card]
    rw [mul_pow, h1]
  have hrk : A.rank ≤ Ap.rank := by
    rw [hfrob]; exact rank_le_rank_map (frobenius E p) A
  -- kernels
  have hnull : ∀ B : Matrix (Fin m) (Fin k) E,
      B.rank + Module.finrank E (LinearMap.ker B.mulVecLin) = k := by
    intro B
    have := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    simpa [Matrix.rank] using this
  set W : Submodule E (Fin k → E) := LinearMap.ker A.mulVecLin with hW
  set W' : Submodule E (Fin k → E) := LinearMap.ker Ap.mulVecLin with hW'
  have hWW' : W ≤ W' := by
    intro w hw
    rw [hW, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    rw [hW', LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hyp w hw
  have hfin : Module.finrank E W' ≤ Module.finrank E W := by
    have h1 : A.rank + Module.finrank E W = k := hnull A
    have h2 : Ap.rank + Module.finrank E W' = k := hnull Ap
    omega
  have hEq : W = W' := Submodule.eq_of_le_of_finrank_le hWW' hfin
  have hstable : ∀ w ∈ W, (fun i => w i ^ p) ∈ W := by
    intro w hw
    rw [hEq, hW', LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [hW, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    ext u
    have h0 : (A.mulVec w) u = 0 := by rw [hw]; rfl
    have : (Ap.mulVec (fun i => w i ^ p)) u = ((A.mulVec w) u) ^ p := by
      simp only [Matrix.mulVec, dotProduct, hfrob, Matrix.map_apply, frobenius_def, sum_pow_char,
        mul_pow]
    rw [this, h0]
    simp [(Fact.out : p.Prime).ne_zero]
  obtain ⟨b, hbli, hbmem⟩ := frob_descent W hstable
  have hstack : ∀ l, (stackM N).mulVec (b l) = 0 := by
    intro l
    have hm := hbmem l
    rw [hW, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hm
    ext ⟨i, u⟩
    have h1 := congrFun hm u
    -- rewrite as evaluation of a polynomial
    have h2 : (A.mulVec (fun i => algebraMap (ZMod p) E (b l i))) u =
        evP (∑ j, X j * C (∑ v, N j u v * b l v)) := by
      simp only [Matrix.mulVec, dotProduct, hA, pencilE, Matrix.of_apply, pow_one, map_sum,
        map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
      simp [hlam, Algebra.algebraMap_eq_smul_one, RingHom.algebraMap_toAlgebra]
      ring
    have h3 : (∑ j, X j * C (∑ v, N j u v * b l v) : MvPolynomial (Fin s) (ZMod p)) = 0 := by
      apply hev
      rw [← h2, map_zero]
      simpa using h1
    have h4 := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h3
    simp only [MvPolynomial.coeff_sum, coeff_zero] at h4
    have h5 : ∀ j, MvPolynomial.coeff (Finsupp.single i 1)
        (X j * C (∑ v, N j u v * b l v) : MvPolynomial (Fin s) (ZMod p)) =
        if j = i then ∑ v, N j u v * b l v else 0 := by
      intro j
      rw [MvPolynomial.coeff_X_mul']
      by_cases hji : j = i
      · subst hji
        have hmem : j ∈ (Finsupp.single j 1).support := by simp
        rw [if_pos hmem, if_pos rfl, tsub_self, MvPolynomial.coeff_zero_C]
      · have hnm : j ∉ (Finsupp.single i 1).support := by
          simp [Finsupp.single_apply, hji]
        rw [if_neg hnm, if_neg hji]
    simp only [h5] at h4
    simpa using h4
  -- dimension count
  set K : Submodule (ZMod p) (Fin k → ZMod p) := LinearMap.ker (stackM N).mulVecLin with hK
  have hmemK : ∀ l, b l ∈ K := by
    intro l
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hstack l
  have hli' : LinearIndependent (ZMod p) (fun l => (⟨b l, hmemK l⟩ : K)) := by
    apply LinearIndependent.of_comp K.subtype
    exact hbli
  have hcard := hli'.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  have hnull2 : (stackM N).rank + Module.finrank (ZMod p) K = k := by
    have := LinearMap.finrank_range_add_finrank_ker (stackM N).mulVecLin
    simpa [Matrix.rank] using this
  have h1 : A.rank + Module.finrank E W = k := hnull A
  omega

end Descent

section Final
open MvPolynomial
variable {p : ℕ} [Fact p.Prime] {s m k : ℕ}

/-- The field `F_p(λ_1, …, λ_s)`. -/
abbrev FRat (p s : ℕ) [Fact p.Prime] := FractionRing (MvPolynomial (Fin s) (ZMod p))

/-- The embedding `F_p[λ] → F_p(λ)`. -/
noncomputable abbrev evFR (p s : ℕ) [Fact p.Prime] :
    MvPolynomial (Fin s) (ZMod p) →+* FRat p s :=
  algebraMap (MvPolynomial (Fin s) (ZMod p)) (FRat p s)

theorem pang_rank_retention (N : Fin s → Matrix (Fin m) (Fin k) (ZMod p))
    (hyp : ∀ u : Fin k → FRat p s,
      (pencilE (fun i => evFR p s (X i)) 1 ((evFR p s).comp C) N).mulVec u = 0 →
      (pencilE (fun i => evFR p s (X i)) p ((evFR p s).comp C) N).mulVec u = 0) :
    ∃ c : Fin s → ZMod p, (stackM N).rank * (p - 1) ≤ p * (pencilAt N c).rank := by
  classical
  have hinj : Function.Injective (evFR p s) := IsFractionRing.injective _ _
  have hdesc := pencil_descent_rank (evFR p s) hinj N hyp
  set A := pencilE (fun i => evFR p s (X i)) 1 ((evFR p s).comp C) N with hA
  have hAmap : A = (pencilPoly N).map (evFR p s) := by
    ext u v
    simp [hA, pencilE, pencilPoly]
  obtain ⟨r, c, hdet⟩ := exists_minor A
  have hdet' : ((pencilPoly N).submatrix r c).det ≠ 0 := by
    intro h0
    apply hdet
    have : A.submatrix r c = ((pencilPoly N).submatrix r c).map (evFR p s) := by
      ext i j
      have := congrFun (congrFun hAmap (r i)) (c j)
      simpa [Matrix.map_apply] using this
    rw [this]
    have e := (evFR p s).map_det ((pencilPoly N).submatrix r c)
    rw [RingHom.mapMatrix_apply] at e
    rw [← e, h0, map_zero]
  have hsum := pencil_sum N r c hdet'
  set R := A.rank with hR
  have hq : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_contra hcon
  push Not at hcon
  have hlt : ∀ a : Fin s → ZMod p, p * (pencilAt N a).rank < R * (p - 1) := by
    intro a
    have := hcon a
    calc p * (pencilAt N a).rank < (stackM N).rank * (p - 1) := this
      _ ≤ R * (p - 1) := Nat.mul_le_mul_right _ hdesc
  have hsl : ∑ a : Fin s → ZMod p, p * (pencilAt N a).rank <
      ∑ _a : Fin s → ZMod p, R * (p - 1) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ => hlt a)
  rw [← Finset.mul_sum] at hsl
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  have hc2 : Fintype.card (Fin s → ZMod p) = p ^ s := by simp [hc]
  rw [Finset.sum_const, Finset.card_univ, hc2, smul_eq_mul] at hsl
  rw [hc] at hsum
  have : R * p ^ (s + 1) = p ^ s * (R * (p - 1)) + R * p ^ s := by
    obtain ⟨t, ht⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
    subst ht
    simp only [Nat.add_sub_cancel]
    ring
  omega

end Final

end Pang
