import Theory.ProofComplexity.PangApprox

/-!
# Pang route, layer G (part 1): evaluation on the cube and indicator polynomials

`indPt a` is the Boolean point whose set of ones is `a`.  `ev (ml g) = eval g` at Boolean points,
so a polynomial of degree `≤ D` that vanishes on every Boolean point lies in `C_D`
(`cd_of_cube`).  `gInd h = polyOf (ml (1 - h^(p-1)))` is Pang's indicator `g_h` of `h = 0`.
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- The Boolean point with ones exactly on `a`. -/
def indPt (a : Set ℕ) : ℕ → ZMod p := fun i => if i ∈ a then 1 else 0

lemma ev_ml_eq (a : Set ℕ) (g : PP p) : PCL.ev a (PCL.ml g) = eval (indPt a) g := by
  induction g using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [ml_monomial, ev_single, eval_monomial]
    unfold Finsupp.prod
    by_cases h : (↑m.support : Set ℕ) ⊆ a
    · rw [if_pos h, Finset.prod_eq_one, mul_one]
      intro i hi
      have : i ∈ a := h hi
      simp [indPt, this]
    · rw [if_neg h]
      obtain ⟨i, hi, hia⟩ := Set.not_subset.1 h
      rw [Finset.prod_eq_zero (i := i) (by exact_mod_cast hi)]
      · simp
      · have hm : m i ≠ 0 := Finsupp.mem_support_iff.1 (by exact_mod_cast hi)
        simp [indPt, hia, zero_pow hm]
  | add a' b ha hb => rw [map_add, map_add, ha, hb, map_add]

lemma eval_polyOf (a : Set ℕ) (f : ML (ZMod p)) : eval (indPt a) (polyOf f) = PCL.ev a f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single S c =>
    rw [polyOf_single, ev_single, map_mul, eval_C, map_prod]
    by_cases h : (↑S : Set ℕ) ⊆ a
    · rw [if_pos h, Finset.prod_eq_one, mul_one]
      intro i hi
      have : i ∈ a := h (by exact_mod_cast hi)
      simp [indPt, this]
    · rw [if_neg h]
      obtain ⟨i, hi, hia⟩ := Set.not_subset.1 h
      rw [Finset.prod_eq_zero (i := i) (by exact_mod_cast hi)]
      · simp
      · simp [indPt, hia]

variable {Ax : Set (PP p)} {D : ℕ}

/-- A polynomial of degree `≤ D` vanishing on the Boolean cube lies in `C_D`. -/
lemma cd_of_cube (hD : 2 ≤ D) {u : PP p} (hu : u.totalDegree ≤ D)
    (h : ∀ a : Set ℕ, eval (indPt a) u = 0) : u ∈ CD Ax D := by
  refine cd_of_ml_eq_zero hD hu (PCL.eq_zero_of_ev fun a => ?_)
  rw [ev_ml_eq]; exact h a

/-- Pang's indicator `g_h = ML(1 - h^{p-1})` of the equation `h = 0`. -/
def gInd (h : PP p) : PP p := polyOf (PCL.ml (1 - h ^ (p - 1)))

lemma eval_gInd (a : Set ℕ) (h : PP p) :
    eval (indPt a) (gInd h) = 1 - (eval (indPt a) h) ^ (p - 1) := by
  unfold gInd
  rw [eval_polyOf, ev_ml_eq]; simp

lemma eval_gInd_eq (a : Set ℕ) (h : PP p) :
    eval (indPt a) (gInd h) = if eval (indPt a) h = 0 then 1 else 0 := by
  rw [eval_gInd]
  by_cases h0 : eval (indPt a) h = 0
  · have : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [if_pos h0, h0, zero_pow (by omega)]; simp
  · rw [if_neg h0, ZMod.pow_card_sub_one_eq_one h0]; simp

lemma totalDegree_gInd {h : PP p} (hh : h.totalDegree ≤ 1) : (gInd h).totalDegree ≤ p - 1 := by
  unfold gInd
  refine (totalDegree_polyOf_le _).trans ?_
  refine PCL.deg_le fun T hT => (card_le_totalDegree hT).trans ?_
  refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_pow _ _).trans ?_
  nlinarith

lemma vars_gInd {V : Finset ℕ} {h : PP p} (hh : h.totalDegree ≤ 1) (hv : ∀ v ∈ h.vars, v ∈ V) :
    ∀ v ∈ (gInd h).vars, v ∈ V := by
  have hmem : PCL.ml (1 - h ^ (p - 1)) ∈ Vk (F := ZMod p) V (p - 1) := by
    refine ml_mem_Vk (fun v hvv => ?_) ?_
    · have := Finset.mem_of_subset (vars_sub_subset ..) hvv
      rcases Finset.mem_union.1 this with h1 | h1
      · simp at h1
      · exact hv v (vars_pow _ _ h1)
    · refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
      refine (totalDegree_pow _ _).trans ?_
      nlinarith
  exact fun v hvv => vars_polyOf_subset ⟨_, hmem⟩ hvv

lemma gInd_const {c : ZMod p} (hc : c ≠ 0) : gInd (C c : PP p) = 0 := by
  unfold gInd
  rw [← C_pow, ZMod.pow_card_sub_one_eq_one hc]
  simp

end

end Pang
