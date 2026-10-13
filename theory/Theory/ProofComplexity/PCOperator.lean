import Theory.ProofComplexity.PCReduction
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Razborov's operator criterion for polynomial calculus degree (Ladder Rung R4, AR-A, layer 3)

Alekhnovich-Razborov Lemma 2.10 ([Raz98]): if a linear operator `R` on multilinear polynomials kills
the axioms, satisfies `R(x_i t) = R(x_i R(t))` for terms `t` of degree `< D`, and does not kill `1`,
then there is no polynomial calculus refutation of degree `≤ D`.

LOG: R4 AR-A operator criterion
-/

namespace SATurday.ProofComplexity.PCL

open Finset MvPolynomial

noncomputable section
open Classical

variable {F : Type} [Field F]

theorem ml_C_mul (a : F) (p : MvPolynomial ℕ F) : ml (C a * p) = a • ml p := by
  rw [MvPolynomial.C_mul', map_smul]

/-- Every term of the multilinearization of `f` has degree below `d` when `X i * f` has degree `≤ d`. -/
theorem card_lt_of_mul {i d : ℕ} {f : MvPolynomial ℕ F} (h : (X i * f).totalDegree ≤ d)
    {T : Finset ℕ} (hT : T ∈ (ml f).support) : T.card < d := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hT
    simp at hT
  have := totalDegree_mul_of_isDomain (X_ne_zero i) hf
  rw [totalDegree_X] at this
  have h2 := card_le_totalDegree hT
  omega

/-- **Lemma 2.10 (Razborov's operator criterion)**, in the form used for induction over derivations. -/
theorem pcd_R_zero {Ax : Set (MvPolynomial ℕ F)} (R : ML F →ₗ[F] ML F) (D : ℕ)
    (h1 : ∀ p ∈ Ax, R (ml p) = 0)
    (h2 : ∀ (T : Finset ℕ) (i : ℕ), T.card < D →
      R (shl {i} (Finsupp.single T 1)) = R (shl {i} (R (Finsupp.single T 1)))) :
    ∀ {d : ℕ} {p : MvPolynomial ℕ F}, d ≤ D → PCD Ax d p → R (ml p) = 0 := by
  intro d p hdD h
  induction h with
  | ax hf _ => exact h1 _ hf
  | bool i _ => rw [ml_bool, map_zero]
  | lin a b _ _ ihf ihg => rw [map_add, ml_C_mul, ml_C_mul, map_add, map_smul, map_smul, ihf, ihg]; simp
  | @mul f i _ hdeg ih =>
    rw [ml_X_mul]
    have hcard : ∀ T ∈ (ml f).support, T.card < D := fun T hT =>
      lt_of_lt_of_le (card_lt_of_mul hdeg hT) hdD
    have key : R (shl {i} (ml f)) = R (shl {i} (R (ml f))) := by
      have hsum : ml f = ∑ T ∈ (ml f).support, Finsupp.single T ((ml f) T) :=
        (Finsupp.sum_single (ml f)).symm
      have e : ∀ T ∈ (ml f).support,
          R (shl {i} (Finsupp.single T ((ml f) T))) =
            R (shl {i} (R (Finsupp.single T ((ml f) T)))) := by
        intro T hT
        have : Finsupp.single T ((ml f) T) = (ml f) T • Finsupp.single T (1 : F) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [this, map_smul, map_smul, map_smul, map_smul, map_smul, h2 T i (hcard T hT)]
      conv_lhs => rw [hsum]
      conv_rhs => rw [hsum]
      simp only [map_sum]
      exact Finset.sum_congr rfl e
    rw [key, ih]
    simp

/-- **Operator criterion**: no refutation of degree `≤ D`. -/
theorem no_refutation_of_operator {Ax : Set (MvPolynomial ℕ F)} (R : ML F →ₗ[F] ML F) (D : ℕ)
    (h1 : ∀ p ∈ Ax, R (ml p) = 0)
    (h2 : ∀ (T : Finset ℕ) (i : ℕ), T.card < D →
      R (shl {i} (Finsupp.single T 1)) = R (shl {i} (R (Finsupp.single T 1))))
    (h3 : R (Finsupp.single ∅ 1) ≠ 0) : ¬ PCD Ax D 1 := by
  intro h
  have := pcd_R_zero R D h1 h2 le_rfl h
  rw [ml_one] at this
  exact h3 this

end

end SATurday.ProofComplexity.PCL
