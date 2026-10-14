import Theory.ProofComplexity.PangMult
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-
# Pang route, layer D (part 2): rank specialization of a linear pencil (Pang Lemma 3.1)

`OrdGe k f` : `f` vanishes to order at least `k` at the origin.  `sq_deficit` : for a scalar
square matrix `A` and a matrix `L` of order-1 entries, `det (A + L)` vanishes to order at least
`R - rank A` (Gauss elimination by transvections).  `deficit_le_mult` turns this into
`R - rank M(a) <= mult a H` for a nonzero `R x R` minor `H` of the generic pencil, and
`pencil_sum` is the averaged form `E_a rank M(a) >= (1 - 1/q) R`.
-/
open MvPolynomial Finset
namespace Pang
variable {F : Type*} [Field F] {σ : Type*}

def deg (d : σ →₀ ℕ) : ℕ := d.sum fun _ e => e

lemma deg_add (d e : σ →₀ ℕ) : deg (d + e) = deg d + deg e := by
  unfold deg; exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

lemma deg_zero : deg (0 : σ →₀ ℕ) = 0 := by simp [deg]

def OrdGe (k : ℕ) (f : MvPolynomial σ F) : Prop := ∀ d : σ →₀ ℕ, deg d < k → coeff d f = 0

lemma OrdGe.zero (k : ℕ) : OrdGe k (0 : MvPolynomial σ F) := fun d _ => by simp

lemma OrdGe.zero_order (f : MvPolynomial σ F) : OrdGe 0 f := fun d h => by omega

lemma OrdGe.add {k : ℕ} {f g : MvPolynomial σ F} (hf : OrdGe k f) (hg : OrdGe k g) :
    OrdGe k (f + g) := fun d h => by simp [hf d h, hg d h]

lemma OrdGe.mono {k l : ℕ} {f : MvPolynomial σ F} (h : OrdGe l f) (hkl : k ≤ l) : OrdGe k f :=
  fun d hd => h d (by omega)

lemma OrdGe.mul {k l : ℕ} {f g : MvPolynomial σ F} (hf : OrdGe k f) (hg : OrdGe l g) :
    OrdGe (k + l) (f * g) := by
  classical
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have : deg x.1 + deg x.2 = deg d := by rw [← hx, deg_add]
  by_cases h1 : deg x.1 < k
  · simp [hf _ h1]
  · have h2 : deg x.2 < l := by omega
    simp [hg _ h2]

lemma OrdGe.smul_C {k : ℕ} {f : MvPolynomial σ F} (a : F) (hf : OrdGe k f) : OrdGe k (C a * f) := by
  intro d hd; rw [coeff_C_mul, hf d hd, mul_zero]

lemma OrdGe.sum {ι : Type*} (S : Finset ι) {k : ℕ} {f : ι → MvPolynomial σ F}
    (h : ∀ i ∈ S, OrdGe k (f i)) : OrdGe k (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using OrdGe.zero k
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

lemma OrdGe.prod {ι : Type*} (S : Finset ι) {k : ι → ℕ} {f : ι → MvPolynomial σ F}
    (h : ∀ i ∈ S, OrdGe (k i) (f i)) : OrdGe (∑ i ∈ S, k i) (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro d hd; simp at hd
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

lemma deg_eq_zero {d : σ →₀ ℕ} (h : deg d < 1) : d = 0 := by
  ext i
  by_contra hne
  have hi : i ∈ d.support := by simpa using hne
  have : d i ≤ deg d := by
    unfold deg
    rw [Finsupp.sum]
    exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) hi
  have : 0 < d i := Nat.pos_of_ne_zero (by simpa using hne)
  simp at *
  omega

lemma ordGe_one_iff (f : MvPolynomial σ F) : OrdGe 1 f ↔ constantCoeff f = 0 := by
  rw [constantCoeff_eq]
  constructor
  · intro h
    exact h 0 (by simp [deg_zero])
  · intro h d hd
    rw [deg_eq_zero hd]; exact h

lemma OrdGe.neg {k : ℕ} {f : MvPolynomial σ F} (hf : OrdGe k f) : OrdGe k (-f) :=
  fun d hd => by simp [hf d hd]

lemma ordGe_det {R : ℕ} (B : Matrix (Fin R) (Fin R) (MvPolynomial σ F)) (Z : Finset (Fin R))
    (h : ∀ i ∈ Z, ∀ j, OrdGe 1 (B i j)) : OrdGe Z.card (B.det) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply OrdGe.sum
  intro p _
  have hp : OrdGe Z.card (∏ i, Matrix.transpose B (p i) i) := by
    have := OrdGe.prod (Finset.univ : Finset (Fin R)) (k := fun i => if i ∈ Z then 1 else 0)
      (f := fun i => Matrix.transpose B (p i) i) (by
        intro i _
        by_cases hi : i ∈ Z
        · simpa [hi] using h i hi (p i)
        · simpa [hi] using OrdGe.zero_order _)
    simpa [Finset.sum_boole] using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h1 | h1
  · simpa [h1] using hp
  · simpa [h1] using hp.neg

open Matrix in
lemma sq_deficit {R : ℕ} (A : Matrix (Fin R) (Fin R) F) (L : Matrix (Fin R) (Fin R) (MvPolynomial σ F))
    (hL : ∀ u v, OrdGe 1 (L u v)) :
    OrdGe (R - A.rank) (A.map C + L).det := by
  classical
  obtain ⟨Ls, Ls', D, hA⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  set U : Matrix (Fin R) (Fin R) F := (Ls.map Matrix.TransvectionStruct.toMatrix).prod with hU
  set V : Matrix (Fin R) (Fin R) F := (Ls'.map Matrix.TransvectionStruct.toMatrix).prod with hV
  have hUd : U.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod Ls
  have hVd : V.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod Ls'
  have hUu : IsUnit U.det := by rw [hUd]; exact isUnit_one
  have hVu : IsUnit V.det := by rw [hVd]; exact isUnit_one
  have hrank : A.rank = (Matrix.diagonal D).rank := by
    rw [hA, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hVu,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUu]
  rw [Matrix.rank_diagonal] at hrank
  set Z : Finset (Fin R) := Finset.univ.filter (fun i => D i = 0) with hZ
  have hZcard : Z.card = R - A.rank := by
    have h1 := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin R)))
      (fun i => D i = 0)
    rw [hrank, Fintype.card_subtype]
    simp only [ne_eq, Finset.card_univ, Fintype.card_fin] at h1 ⊢
    rw [hZ]; omega
  -- factorization
  have hfac : A.map C + L = U.map C * ((Matrix.diagonal D * V).map C + (U⁻¹).map C * L) := by
    have h1 : (U.map C : Matrix (Fin R) (Fin R) (MvPolynomial σ F)) * ((Matrix.diagonal D * V).map C) = A.map C := by
      rw [← Matrix.map_mul, ← Matrix.mul_assoc, ← hA]
    have h2 : (U.map C : Matrix (Fin R) (Fin R) (MvPolynomial σ F)) * ((U⁻¹).map C * L) = L := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hUu]
      simp
    rw [Matrix.mul_add, h1, h2]
  have hdetU : (U.map C : Matrix (Fin R) (Fin R) (MvPolynomial σ F)).det = 1 := by
    have := (C : F →+* MvPolynomial σ F).map_det U
    rw [hUd] at this
    simpa using this.symm
  rw [hfac, Matrix.det_mul, hdetU, one_mul]
  rw [← hZcard]
  apply ordGe_det _ Z
  intro i hi j
  have hDi : D i = 0 := by simpa [hZ] using hi
  have e : ((Matrix.diagonal D * V).map C : Matrix (Fin R) (Fin R) (MvPolynomial σ F)) i j = 0 := by
    simp [Matrix.diagonal_mul, hDi]
  rw [Matrix.add_apply, e, zero_add, Matrix.mul_apply]
  apply OrdGe.sum
  intro l _
  exact (hL l j).smul_C _

open Matrix

variable {s m k : ℕ}

/-- Generic pencil `sum_i X_i M_i` with polynomial entries. -/
noncomputable def pencilPoly (M : Fin s → Matrix (Fin m) (Fin k) F) :
    Matrix (Fin m) (Fin k) (MvPolynomial (Fin s) F) :=
  Matrix.of fun u v => ∑ i, X i * C (M i u v)

/-- The pencil specialized at `a`. -/
def pencilAt (M : Fin s → Matrix (Fin m) (Fin k) F) (a : Fin s → F) : Matrix (Fin m) (Fin k) F :=
  Matrix.of fun u v => ∑ i, a i * M i u v

lemma shift_pencilPoly (M : Fin s → Matrix (Fin m) (Fin k) F) (a : Fin s → F) (u : Fin m)
    (v : Fin k) :
    shift a (pencilPoly M u v) = C (pencilAt M a u v) + pencilPoly M u v := by
  simp only [pencilPoly, pencilAt, Matrix.of_apply, map_sum, map_mul, shift_X, add_mul,
    Finset.sum_add_distrib, map_sum, C_mul]
  rw [add_comm]
  simp [shift]

lemma constantCoeff_pencilPoly (M : Fin s → Matrix (Fin m) (Fin k) F) (u : Fin m) (v : Fin k) :
    constantCoeff (pencilPoly M u v) = 0 := by
  simp [pencilPoly]

lemma totalDegree_pencilPoly_le (M : Fin s → Matrix (Fin m) (Fin k) F) (u : Fin m) (v : Fin k) :
    (pencilPoly M u v).totalDegree ≤ 1 := by
  classical
  show (∑ i, (X i * C (M i u v) : MvPolynomial (Fin s) F)).totalDegree ≤ 1
  refine (totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le fun i _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp

lemma totalDegree_det_le {R : ℕ} (B : Matrix (Fin R) (Fin R) (MvPolynomial σ F))
    (h : ∀ i j, (B i j).totalDegree ≤ 1) : B.det.totalDegree ≤ R := by
  classical
  rw [Matrix.det_apply]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun p _ => ?_)
  have hp : (∏ i, B (p i) i).totalDegree ≤ R := by
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (B (p i) i).totalDegree ≤ ∑ _i : Fin R, 1 := Finset.sum_le_sum fun i _ => h _ _
      _ = R := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h1 | h1
  · simpa [h1] using hp
  · simpa [h1] using hp

lemma deficit_le_mult (M : Fin s → Matrix (Fin m) (Fin k) F) {R : ℕ} (r : Fin R → Fin m)
    (c : Fin R → Fin k) (hH : ((pencilPoly M).submatrix r c).det ≠ 0) (a : Fin s → F) :
    R - (pencilAt M a).rank ≤ mult a ((pencilPoly M).submatrix r c).det := by
  classical
  set B := (pencilPoly M).submatrix r c with hB
  set A := (pencilAt M a).submatrix r c with hA
  have h1 : shift a B.det = (A.map C + B).det := by
    have := (shift a : MvPolynomial (Fin s) F →ₐ[F] _).toRingHom.map_det B
    rw [show (shift a : MvPolynomial (Fin s) F →ₐ[F] _) B.det = _ from this]
    congr 1
    ext u v
    simp [hB, hA, shift_pencilPoly]
  have h2 : OrdGe (R - A.rank) (shift a B.det) := by
    rw [h1]
    exact sq_deficit A B (fun u v => (ordGe_one_iff _).2 (constantCoeff_pencilPoly M _ _))
  obtain ⟨d, hd, hdc⟩ := mult_spec (a := a) hH
  have : ¬ deg d < R - A.rank := fun hlt => hdc (h2 d hlt)
  have h3 : A.rank ≤ (pencilAt M a).rank := rank_submatrix_le _ _ _
  unfold deg at this
  omega

theorem pencil_sum [Fintype F] [DecidableEq F] (M : Fin s → Matrix (Fin m) (Fin k) F) {R : ℕ}
    (r : Fin R → Fin m) (c : Fin R → Fin k) (hH : ((pencilPoly M).submatrix r c).det ≠ 0) :
    R * Fintype.card F ^ (s + 1) ≤
      Fintype.card F * ∑ a : Fin s → F, (pencilAt M a).rank + R * Fintype.card F ^ s := by
  set q := Fintype.card F with hq
  set H := ((pencilPoly M).submatrix r c).det with hHdef
  have hdeg : H.totalDegree ≤ R :=
    totalDegree_det_le _ (fun i j => totalDegree_pencilPoly_le M _ _)
  have hS := sum_mult_le s H hH
  have hdef : ∑ a : Fin s → F, (R - (pencilAt M a).rank) ≤ ∑ a : Fin s → F, mult a H :=
    Finset.sum_le_sum fun a _ => deficit_le_mult M r c hH a
  have hcard : Fintype.card (Fin s → F) = q ^ s := by simp [hq]
  have hlow : R * q ^ s ≤ ∑ a : Fin s → F, (R - (pencilAt M a).rank) +
      ∑ a : Fin s → F, (pencilAt M a).rank := by
    rw [← Finset.sum_add_distrib]
    calc R * q ^ s = ∑ _a : Fin s → F, R := by simp [hcard, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun a _ => by omega
  have h4 : (∑ a : Fin s → F, mult a H) * q ≤ R * q ^ s :=
    hS.trans (Nat.mul_le_mul_right _ hdeg)
  calc R * q ^ (s + 1) = q * (R * q ^ s) := by ring
    _ ≤ q * (∑ a : Fin s → F, (R - (pencilAt M a).rank) + ∑ a : Fin s → F, (pencilAt M a).rank) :=
        Nat.mul_le_mul_left _ hlow
    _ = q * ∑ a : Fin s → F, (R - (pencilAt M a).rank) + q * ∑ a : Fin s → F, (pencilAt M a).rank := by ring
    _ ≤ R * q ^ s + q * ∑ a : Fin s → F, (pencilAt M a).rank := by
        have : q * ∑ a : Fin s → F, (R - (pencilAt M a).rank) ≤ R * q ^ s := by
          calc _ ≤ q * ∑ a : Fin s → F, mult a H := Nat.mul_le_mul_left _ hdef
            _ = (∑ a : Fin s → F, mult a H) * q := by ring
            _ ≤ _ := h4
        omega
    _ = _ := by ring

end Pang
