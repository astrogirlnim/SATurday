import Theory.ProofComplexity.PolyCalc
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.BitIndices
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Prod.Lex

/-!
# Multilinear polynomials and Boolean points (Ladder Rung R4, AR-A, layer 1)

The algebra `S(F)` of Alekhnovich-Razborov: a multilinear polynomial in the variables `ℕ` is a finitely
supported function from terms (finite sets of variables) to `F`.  A Boolean point is a set `a : Set ℕ`
(the variables set to `1`).  `ev a` evaluates, `shl s` multiplies by the term `s`, `ml` multilinearizes an
`MvPolynomial`.  Terms are totally ordered by `key` (cardinality first, then binary expansion), a
well-founded order refining the degree.

LOG: R4 AR-A multilinear layer
-/

namespace SATurday.ProofComplexity.PCL

open Finset

/-- Multilinear polynomials: finitely supported functions on terms. -/
abbrev ML (F : Type) [Field F] := Finset ℕ →₀ F

noncomputable section
open Classical

variable {F : Type} [Field F]

/-- The degree of a multilinear polynomial. -/
def deg (g : ML F) : ℕ := g.support.sup Finset.card

theorem le_deg {g : ML F} {T : Finset ℕ} (h : T ∈ g.support) : T.card ≤ deg g :=
  Finset.le_sup (f := Finset.card) h

theorem deg_le {g : ML F} {n : ℕ} (h : ∀ T ∈ g.support, T.card ≤ n) : deg g ≤ n :=
  Finset.sup_le h

/-! ## Evaluation -/

/-- Value of the term `T` at the Boolean point `a`. -/
def evT (a : Set ℕ) (T : Finset ℕ) : F := if (↑T : Set ℕ) ⊆ a then 1 else 0

/-- Evaluation at the Boolean point `a` (the set of variables that are `1`). -/
def ev (a : Set ℕ) : ML F →ₗ[F] F := Finsupp.linearCombination F (evT a)

theorem ev_single (a : Set ℕ) (T : Finset ℕ) (c : F) :
    ev a (Finsupp.single T c) = if (↑T : Set ℕ) ⊆ a then c else 0 := by
  unfold ev
  rw [Finsupp.linearCombination_single]
  unfold evT
  split_ifs <;> simp

theorem ev_apply (a : Set ℕ) (g : ML F) :
    ev a g = ∑ T ∈ g.support, if (↑T : Set ℕ) ⊆ a then g T else 0 := by
  conv_lhs => rw [← Finsupp.sum_single g]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [ev_single]

/-- A multilinear polynomial vanishing at every Boolean point is zero. -/
theorem eq_zero_of_ev {g : ML F} (h : ∀ a, ev a g = 0) : g = 0 := by
  by_contra hg
  obtain ⟨T0, hT0, hmin⟩ := Finset.exists_min_image g.support Finset.card
    (Finsupp.support_nonempty_iff.2 hg)
  have := h (↑T0 : Set ℕ)
  rw [ev_apply, Finset.sum_eq_single T0] at this
  · simp at this
    exact (Finsupp.mem_support_iff.1 hT0) this
  · intro T hT hne
    split_ifs with hs
    · exfalso
      have hsub : T ⊆ T0 := by exact_mod_cast hs
      have h1 := hmin T hT
      exact hne (Finset.eq_of_subset_of_card_le hsub h1)
    · rfl
  · intro hn; exact absurd hT0 hn

/-! ## Multiplication by a term -/

/-- Multiplication by the term `s` (multilinear: `x² = x`). -/
def shl (s : Finset ℕ) : ML F →ₗ[F] ML F := Finsupp.lmapDomain F F (· ∪ s)

theorem shl_single (s T : Finset ℕ) (c : F) :
    shl s (Finsupp.single T c) = Finsupp.single (T ∪ s) c := by
  simp [shl]

theorem ev_shl (a : Set ℕ) (s : Finset ℕ) (g : ML F) :
    ev a (shl s g) = if (↑s : Set ℕ) ⊆ a then ev a g else 0 := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; split_ifs <;> simp
  | single T c =>
    rw [shl_single, ev_single, ev_single]
    by_cases hs : (↑s : Set ℕ) ⊆ a
    · simp [hs, Finset.coe_union]
    · have : ¬ (↑(T ∪ s) : Set ℕ) ⊆ a := by
        intro h; apply hs; intro x hx; exact h (by simp [hx])
      simp [hs, this]

theorem support_shl_subset (s : Finset ℕ) (g : ML F) :
    ∀ U ∈ (shl s g).support, ∃ T ∈ g.support, U = T ∪ s := by
  intro U hU
  have := Finsupp.mapDomain_support hU
  simp only [Finset.mem_image] at this
  obtain ⟨T, hT, h⟩ := this
  exact ⟨T, hT, h.symm⟩

/-! ## Killing the terms outside a set of variables -/

/-- Keep only the terms inside `W`. -/
def kW (W : Set ℕ) : ML F →ₗ[F] ML F where
  toFun g := g.filter fun T : Finset ℕ => (↑T : Set ℕ) ⊆ W
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem kW_apply (W : Set ℕ) (g : ML F) (T : Finset ℕ) :
    kW W g T = if (↑T : Set ℕ) ⊆ W then g T else 0 := rfl

theorem support_kW (W : Set ℕ) (g : ML F) :
    (kW W g).support = g.support.filter fun T : Finset ℕ => (↑T : Set ℕ) ⊆ W := rfl

theorem ev_kW (W a : Set ℕ) (g : ML F) : ev a (kW W g) = ev (a ∩ W) g := by
  rw [ev_apply, ev_apply, support_kW, Finset.sum_filter]
  have : ∀ T : Finset ℕ, ((↑T : Set ℕ) ⊆ a ∩ W) ↔ ((↑T : Set ℕ) ⊆ W ∧ (↑T : Set ℕ) ⊆ a) := by
    intro T; rw [Set.subset_inter_iff]; tauto
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [kW_apply, this]
  by_cases h1 : (↑T : Set ℕ) ⊆ W <;> by_cases h2 : (↑T : Set ℕ) ⊆ a <;> simp [h1, h2]

/-! ## Multilinearization of polynomials -/

/-- The multilinear reduction of a polynomial: each monomial goes to its set of variables. -/
def ml : MvPolynomial ℕ F →ₗ[F] ML F where
  toFun p := Finsupp.mapDomain (fun m : ℕ →₀ ℕ => m.support) p
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' c p := Finsupp.mapDomain_smul c p

theorem ml_monomial (m : ℕ →₀ ℕ) (c : F) :
    ml (MvPolynomial.monomial m c) = Finsupp.single m.support c := by
  show Finsupp.mapDomain (fun m : ℕ →₀ ℕ => m.support) (Finsupp.single m c) = _
  rw [Finsupp.mapDomain_single]

theorem ml_X_mul (i : ℕ) (p : MvPolynomial ℕ F) :
    ml (MvPolynomial.X i * p) = shl {i} (ml p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, ml_monomial, ml_monomial, shl_single]
    congr 1
    ext j
    simp only [Finsupp.mem_support_iff, Finset.mem_union, Finset.mem_singleton, Finsupp.coe_add,
      Pi.add_apply, Finsupp.single_apply]
    by_cases hj : i = j <;> simp [hj, eq_comm]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, map_add]

theorem ml_bool (i : ℕ) : ml (MvPolynomial.X i ^ 2 - MvPolynomial.X i : MvPolynomial ℕ F) = 0 := by
  have h1 : (MvPolynomial.X i ^ 2 : MvPolynomial ℕ F) = MvPolynomial.monomial (Finsupp.single i 2) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.X i : MvPolynomial ℕ F) = MvPolynomial.monomial (Finsupp.single i 1) 1 := rfl
  rw [map_sub, h1, h2, ml_monomial, ml_monomial, Finsupp.support_single_ne_zero _ (by norm_num),
    Finsupp.support_single_ne_zero _ (by norm_num), sub_self]

theorem ml_one : ml (1 : MvPolynomial ℕ F) = Finsupp.single ∅ 1 := by
  have : (1 : MvPolynomial ℕ F) = MvPolynomial.monomial 0 1 := rfl
  rw [this, ml_monomial]; simp

theorem support_ml_subset (p : MvPolynomial ℕ F) :
    ∀ T ∈ (ml p).support, ∃ m ∈ p.support, T = m.support := by
  intro T hT
  have := Finsupp.mapDomain_support hT
  simp only [Finset.mem_image] at this
  obtain ⟨m, hm, h⟩ := this
  exact ⟨m, hm, h.symm⟩

theorem card_le_totalDegree {p : MvPolynomial ℕ F} {T : Finset ℕ} (hT : T ∈ (ml p).support) :
    T.card ≤ p.totalDegree := by
  obtain ⟨m, hm, rfl⟩ := support_ml_subset p T hT
  refine le_trans ?_ (MvPolynomial.le_totalDegree hm)
  unfold Finsupp.sum
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)

end

end SATurday.ProofComplexity.PCL
