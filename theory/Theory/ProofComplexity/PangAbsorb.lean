import Theory.ProofComplexity.PCMultilinear
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Algebra.Ring.GeomSum

/-!
# Pang route, layer B: the space `C_D` of degree `D` consequences

For `Ax` a set of polynomial axioms over a field, `CD Ax D` is the `F`-subspace of polynomials that
are `0` or have a degree `D` polynomial calculus derivation (with built in Boolean axioms) from `Ax`.
This is Pang's `C_D` (Preliminaries, l.208).

* `cd_mul` : Fact 2.1 (absorption): `f ∈ C_D`, `deg f + deg g ≤ D` gives `g f ∈ C_D`.
* `cd_of_ml_eq_zero` : Fact 2.2 (Boolean reduction): if `2 ≤ D`, `deg f ≤ D` and the multilinearization
  of `f` vanishes (`f` vanishes on the cube) then `f ∈ C_D`, for any axiom set.
* `cd_frobenius` : the displayed consequence (2.3): over `ZMod p`, `deg g ≤ d`, `p d ≤ D`, `2 ≤ D`
  give `g^p - g ∈ C_D`.
-/

open SATurday.ProofComplexity
namespace Pang
open MvPolynomial

noncomputable section

section CD
variable {F : Type} [Field F] (Ax : Set (MvPolynomial ℕ F)) (D : ℕ)

/-- Pang's `C_D`: the polynomials with a degree `D` derivation (together with `0`). -/
def CD : Submodule F (MvPolynomial ℕ F) where
  carrier := {f | f = 0 ∨ PCD Ax D f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro f g (rfl | hf) (rfl | hg)
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using hg)
    · exact Or.inr (by simpa using hf)
    · right
      have := PCD.lin 1 1 hf hg
      simpa using this
  smul_mem' := by
    rintro c f (rfl | hf)
    · exact Or.inl (by simp)
    · right
      have := PCD.lin c 0 hf hf
      simpa [MvPolynomial.smul_eq_C_mul] using this

variable {Ax D}

theorem mem_CD_of_pcd {f : MvPolynomial ℕ F} (h : PCD Ax D f) : f ∈ CD Ax D := Or.inr h

theorem totalDegree_le_of_mem_CD {f : MvPolynomial ℕ F} (h : f ∈ CD Ax D) : f.totalDegree ≤ D := by
  rcases h with rfl | h
  · simp
  · exact pcd_deg h

theorem cd_X_mul {f : MvPolynomial ℕ F} (hf : f ∈ CD Ax D) (i : ℕ)
    (hd : (X i * f).totalDegree ≤ D) : X i * f ∈ CD Ax D := by
  rcases hf with rfl | hf
  · exact Or.inl (by simp)
  · exact Or.inr (PCD.mul i hf hd)

theorem cd_monomial_mul {g : MvPolynomial ℕ F} (hg : g ∈ CD Ax D) :
    ∀ m (s : ℕ →₀ ℕ), Finsupp.degree s = m → m + g.totalDegree ≤ D →
      monomial s 1 * g ∈ CD Ax D := by
  intro m
  induction m with
  | zero =>
    intro s hs _
    rw [(Finsupp.degree_eq_zero_iff s).1 hs, monomial_zero', C_1, one_mul]; exact hg
  | succ m ih =>
    intro s hs hD
    have hne : s ≠ 0 := by rintro rfl; simp at hs
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    set t := s - Finsupp.single i 1
    have hst : s = t + Finsupp.single i 1 := by
      ext j; simp only [t, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
    have ht : Finsupp.degree t = m := by
      rw [hst, map_add, Finsupp.degree_single] at hs; omega
    have hmul : monomial s (1 : F) * g = X i * (monomial t 1 * g) := by
      rw [hst, ← mul_assoc, X, monomial_mul, add_comm, one_mul]
    rw [hmul]
    refine cd_X_mul (ih t ht (by omega)) i ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    refine (Nat.add_le_add_left (totalDegree_mul _ _) 1).trans ?_
    rw [totalDegree_monomial _ one_ne_zero]
    have : (t.sum fun _ e => e) = m := ht
    omega

/-- **Absorption** (Pang Fact 2.1): multiplying an element of `C_D` by a polynomial of small degree. -/
theorem cd_mul {f g : MvPolynomial ℕ F} (hf : f ∈ CD Ax D)
    (hD : g.totalDegree + f.totalDegree ≤ D) : g * f ∈ CD Ax D := by
  rw [g.as_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [show monomial s (coeff s g) = C (coeff s g) * monomial s 1 by rw [C_mul_monomial, mul_one],
    mul_assoc, ← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (cd_monomial_mul hf _ s rfl ?_)
  have := le_totalDegree hs
  exact le_trans (Nat.add_le_add_right this _) hD

end CD


section Boolean
variable {F : Type} [Field F] {Ax : Set (MvPolynomial ℕ F)} {D : ℕ}

theorem totalDegree_bool_le (i : ℕ) : (X i ^ 2 - X i : MvPolynomial ℕ F).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans (by rw [totalDegree_X]))
    (by rw [totalDegree_X]; omega))

theorem cd_bool_mul (hD : 2 ≤ D) (i : ℕ) {h : MvPolynomial ℕ F} (hh : h.totalDegree + 2 ≤ D) :
    h * (X i ^ 2 - X i) ∈ CD Ax D := by
  have := cd_mul (Ax := Ax) (D := D) (f := X i ^ 2 - X i) (g := h) (mem_CD_of_pcd (PCD.bool i hD))
    (by have := totalDegree_bool_le (F := F) i; omega)
  exact this

theorem totalDegree_prod_X_pow_le (S : Finset ℕ) (e : ℕ → ℕ) :
    (∏ i ∈ S, (X i : MvPolynomial ℕ F) ^ e i).totalDegree ≤ ∑ i ∈ S, e i := by
  refine (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; simp)

theorem totalDegree_prod_X_le (S : Finset ℕ) :
    (∏ i ∈ S, (X i : MvPolynomial ℕ F)).totalDegree ≤ S.card := by
  refine (totalDegree_finset_prod _ _).trans ?_
  simp only [totalDegree_X, Finset.sum_const, smul_eq_mul, mul_one]; exact le_rfl

/-- Replacing the exponents by `1` on a set of variables costs nothing in `C_D`. -/
theorem cd_prod_pow_sub (hD : 2 ≤ D) (e : ℕ → ℕ) :
    ∀ S : Finset ℕ, (∀ i ∈ S, 1 ≤ e i) → ∑ i ∈ S, e i ≤ D →
      (∏ i ∈ S, (X i : MvPolynomial ℕ F) ^ e i) - ∏ i ∈ S, X i ∈ CD Ax D := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a S ha ih =>
    intro he hsum
    rw [Finset.sum_insert ha] at hsum
    have he' : ∀ i ∈ S, 1 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea : 1 ≤ e a := he a (Finset.mem_insert_self _ _)
    have hih := ih he' (by omega)
    have hcard : S.card ≤ ∑ i ∈ S, e i := by
      rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum he'
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    set P := ∏ i ∈ S, (X i : MvPolynomial ℕ F) ^ e i
    set Q := ∏ i ∈ S, (X i : MvPolynomial ℕ F)
    have hid : X a ^ e a * P - X a * Q = X a ^ e a * (P - Q) +
        (X a ^ 2 - X a) * ((∑ j ∈ Finset.range (e a - 1), X a ^ j) * Q) := by
      have hg : (∑ j ∈ Finset.range (e a - 1), (X a : MvPolynomial ℕ F) ^ j) * (X a - 1) =
          X a ^ (e a - 1) - 1 := geom_sum_mul _ _
      have hpow : (X a : MvPolynomial ℕ F) ^ e a = X a * X a ^ (e a - 1) := by
        rw [← pow_succ']; congr 1; omega
      have : (X a ^ 2 - X a : MvPolynomial ℕ F) * (∑ j ∈ Finset.range (e a - 1), X a ^ j) =
          X a ^ e a - X a := by
        rw [hpow]
        calc (X a ^ 2 - X a : MvPolynomial ℕ F) * (∑ j ∈ Finset.range (e a - 1), X a ^ j)
            = X a * ((∑ j ∈ Finset.range (e a - 1), X a ^ j) * (X a - 1)) := by ring
          _ = X a * (X a ^ (e a - 1) - 1) := by rw [hg]
          _ = _ := by ring
      calc X a ^ e a * P - X a * Q = X a ^ e a * (P - Q) + (X a ^ e a - X a) * Q := by ring
        _ = _ := by rw [← this]; ring
    rw [hid]
    refine add_mem ?_ ?_
    · refine cd_mul hih ?_
      refine le_trans (Nat.add_le_add ((totalDegree_pow _ _).trans (by rw [totalDegree_X]))
        ((totalDegree_sub _ _).trans (max_le (totalDegree_prod_X_pow_le S e)
          ((totalDegree_prod_X_le S).trans hcard)))) ?_
      omega
    · rw [mul_comm]
      refine cd_bool_mul hD a ?_
      rcases Nat.eq_zero_or_pos (e a - 1) with h0 | hpos
      · rw [h0]; simp; omega
      · refine le_trans (Nat.add_le_add_right (totalDegree_mul _ _) 2) ?_
        have h1 : (∑ j ∈ Finset.range (e a - 1), (X a : MvPolynomial ℕ F) ^ j).totalDegree ≤
            e a - 2 := by
          refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j hj => ?_)
          rw [Finset.mem_range] at hj
          exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; omega)
        have : Q.totalDegree ≤ S.card := totalDegree_prod_X_le (F := F) S
        omega

/-- A monomial is congruent to its squarefree part modulo `C_D`. -/
theorem cd_monomial_sub (hD : 2 ≤ D) (m : ℕ →₀ ℕ) (hm : Finsupp.degree m ≤ D) :
    (monomial m 1 : MvPolynomial ℕ F) - ∏ i ∈ m.support, X i ∈ CD Ax D := by
  have h := cd_prod_pow_sub (Ax := Ax) (F := F) hD (fun i => m i) m.support
    (fun i hi => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)) hm
  rw [monomial_eq, C_1, one_mul]
  exact h

/-- The squarefree representative of a polynomial. -/
def mlPoly (f : MvPolynomial ℕ F) : MvPolynomial ℕ F :=
  f.sum fun m c => C c * ∏ i ∈ m.support, X i

theorem mlPoly_eq_zero {f : MvPolynomial ℕ F} (h : PCL.ml f = 0) : mlPoly f = 0 := by
  have h1 : (Finsupp.mapDomain (fun m : ℕ →₀ ℕ => m.support) f).sum
      (fun T c => (C c * ∏ i ∈ T, X i : MvPolynomial ℕ F)) = mlPoly f :=
    Finsupp.sum_mapDomain_index (by intro T; simp) (by intro T a b; rw [C_add, add_mul])
  rw [← h1]
  have : Finsupp.mapDomain (fun m : ℕ →₀ ℕ => m.support) f = 0 := h
  rw [this]; simp

/-- **Boolean reduction** (Pang Fact 2.2): a polynomial of degree `≤ D` that vanishes on the cube
(multilinearization zero) lies in `C_D`, for any axiom set. -/
theorem cd_of_ml_eq_zero (hD : 2 ≤ D) {f : MvPolynomial ℕ F} (hdeg : f.totalDegree ≤ D)
    (h : PCL.ml f = 0) : f ∈ CD Ax D := by
  have h0 := mlPoly_eq_zero h
  have : f = f - mlPoly f := by rw [h0, sub_zero]
  rw [this]
  have hsum : f - mlPoly f = ∑ m ∈ f.support,
      C (coeff m f) * ((monomial m 1 : MvPolynomial ℕ F) - ∏ i ∈ m.support, X i) := by
    have e1 : f = ∑ m ∈ f.support, monomial m (coeff m f) := f.as_sum
    have e2 : mlPoly f = ∑ m ∈ f.support, C (coeff m f) * ∏ i ∈ m.support, (X i : MvPolynomial ℕ F) := rfl
    calc f - mlPoly f = (∑ m ∈ f.support, monomial m (coeff m f)) - mlPoly f := by rw [← e1]
      _ = _ := ?_
    rw [e2]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_sub, C_mul_monomial, mul_one]
  rw [hsum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (cd_monomial_sub hD m ?_)
  have := le_totalDegree hm
  have h2 : Finsupp.degree m = m.sum fun _ e => e := rfl
  omega

end Boolean

section Frobenius
variable {p : ℕ} [Fact p.Prime] {Ax : Set (MvPolynomial ℕ (ZMod p))} {D : ℕ}

theorem ml_pow_char (g : MvPolynomial ℕ (ZMod p)) : PCL.ml (g ^ p) = PCL.ml g := by
  rw [← expand_zmod]
  induction g using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [expand_monomial, PCL.ml_monomial, PCL.ml_monomial]
    rw [Finsupp.support_smul_eq (R := ℕ) (M := ℕ) (b := p) (g := d) (Fact.out : p.Prime).ne_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- **Frobenius** (Pang display (2.3)): `g^p - g ∈ C_D` for `deg g ≤ d`, `p d ≤ D`. -/
theorem cd_frobenius (hD : 2 ≤ D) {g : MvPolynomial ℕ (ZMod p)} {d : ℕ} (hg : g.totalDegree ≤ d)
    (hpd : p * d ≤ D) : g ^ p - g ∈ CD Ax D := by
  refine cd_of_ml_eq_zero hD ?_ (by rw [map_sub, ml_pow_char, sub_self])
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_pow _ _).trans (le_trans (Nat.mul_le_mul_left _ hg) hpd)
  · have : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    nlinarith

end Frobenius

end

end Pang
