import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Theory.ProofComplexity.Resolution

/-!
# Polynomial calculus (Ladder Rung R4, 1C.1)

Polynomial calculus over a field `F` with variables indexed by `ℕ`: from axioms and the Boolean
axioms `x_i² - x_i`, derive by linear combinations and multiplication by a variable; a degree
`d` derivation keeps every line of total degree at most `d` (`PCD Ax d f`). A clause is encoded
by the product of its falsifying factors (`1 - x` for a positive literal, `x` for a negative
one). Soundness: a derivation of `1` rules out a common Boolean root (`pcd_sound`), in particular
a CNF with a degree `d` refutation is unsatisfiable (`pc_cnf_unsat`).

LOG: R4 PolyCalc module (polynomial calculus)
-/

namespace SATurday.ProofComplexity

open MvPolynomial

noncomputable section

variable {F : Type} [Field F]

/-- Degree `d` polynomial calculus derivations from the axioms `Ax`. -/
inductive PCD (Ax : Set (MvPolynomial ℕ F)) (d : ℕ) : MvPolynomial ℕ F → Prop
  | ax {f} : f ∈ Ax → f.totalDegree ≤ d → PCD Ax d f
  | bool (i : ℕ) : 2 ≤ d → PCD Ax d (X i ^ 2 - X i)
  | lin {f g} (a b : F) : PCD Ax d f → PCD Ax d g → PCD Ax d (C a * f + C b * g)
  | mul {f} (i : ℕ) : PCD Ax d f → (X i * f).totalDegree ≤ d → PCD Ax d (X i * f)

/-- Every line of a degree `d` derivation has total degree at most `d`. -/
theorem pcd_deg {Ax : Set (MvPolynomial ℕ F)} {d : ℕ} {f : MvPolynomial ℕ F}
    (h : PCD Ax d f) : f.totalDegree ≤ d := by
  induction h with
  | ax _ hd => exact hd
  | bool i h2 =>
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; omega)
    · rw [totalDegree_X]; omega
  | lin a b _ _ ihf ihg =>
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
    · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  | mul i _ hd _ => exact hd

/-- Polynomial calculus without Boolean axioms (for non Boolean encodings). -/
inductive PCD₀ (Ax : Set (MvPolynomial ℕ F)) (d : ℕ) : MvPolynomial ℕ F → Prop
  | ax {f} : f ∈ Ax → f.totalDegree ≤ d → PCD₀ Ax d f
  | lin {f g} (a b : F) : PCD₀ Ax d f → PCD₀ Ax d g → PCD₀ Ax d (C a * f + C b * g)
  | mul {f} (i : ℕ) : PCD₀ Ax d f → (X i * f).totalDegree ≤ d → PCD₀ Ax d (X i * f)

/-- Boolean polynomial calculus is the plain one with the Boolean axioms added. -/
theorem pcd_to_pcd₀ {Ax : Set (MvPolynomial ℕ F)} {d : ℕ} {f : MvPolynomial ℕ F}
    (h : PCD Ax d f) : PCD₀ (Ax ∪ {g | ∃ i, g = X i ^ 2 - X i}) d f := by
  induction h with
  | ax hf hd => exact PCD₀.ax (Or.inl hf) hd
  | bool i h2 => exact PCD₀.ax (Or.inr ⟨i, rfl⟩) (pcd_deg (PCD.bool (Ax := Ax) i h2))
  | lin a b _ _ ihf ihg => exact PCD₀.lin a b ihf ihg
  | mul i _ hd ih => exact PCD₀.mul i ih hd

/-! ## Closure properties of plain derivations -/

section Closure

variable {Ax : Set (MvPolynomial ℕ F)} {D : ℕ}

theorem pcd₀_zero {g : MvPolynomial ℕ F} (hg : PCD₀ Ax D g) : PCD₀ Ax D 0 := by
  have := PCD₀.lin 0 0 hg hg; simpa using this

theorem pcd₀_add {f g : MvPolynomial ℕ F} (hf : PCD₀ Ax D f) (hg : PCD₀ Ax D g) :
    PCD₀ Ax D (f + g) := by
  have := PCD₀.lin 1 1 hf hg; simpa using this

theorem pcd₀_smul {f : MvPolynomial ℕ F} (a : F) (hf : PCD₀ Ax D f) : PCD₀ Ax D (C a * f) := by
  have := PCD₀.lin a 0 hf hf; simpa using this

theorem pcd₀_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial ℕ F) (h0 : PCD₀ Ax D 0)
    (hf : ∀ i ∈ s, PCD₀ Ax D (f i)) : PCD₀ Ax D (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pcd₀_add (hf a (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem pcd₀_monomial_mul {g : MvPolynomial ℕ F} (hg : PCD₀ Ax D g) :
    ∀ m (s : ℕ →₀ ℕ), Finsupp.degree s = m → m + g.totalDegree ≤ D →
      PCD₀ Ax D (monomial s 1 * g) := by
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
    refine PCD₀.mul i (ih t ht (by omega)) ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    refine (Nat.add_le_add_left (totalDegree_mul _ _) 1).trans ?_
    rw [totalDegree_monomial _ one_ne_zero]
    have : (t.sum fun _ e => e) = m := ht
    omega

/-- Multiplying a derived polynomial by any polynomial of small enough degree. -/
theorem pcd₀_mul {g h : MvPolynomial ℕ F} (hg : PCD₀ Ax D g)
    (hD : h.totalDegree + g.totalDegree ≤ D) : PCD₀ Ax D (h * g) := by
  rw [h.as_sum, Finset.sum_mul]
  refine pcd₀_sum _ _ (pcd₀_zero hg) fun s hs => ?_
  rw [show monomial s (coeff s h) = C (coeff s h) * monomial s 1 by rw [C_mul_monomial, mul_one],
    mul_assoc]
  refine pcd₀_smul _ (pcd₀_monomial_mul hg _ s rfl ?_)
  have := le_totalDegree hs
  exact le_trans (Nat.add_le_add_right this _) hD

end Closure

/-- A Boolean point of `F`. -/
def BoolPt (a : ℕ → F) : Prop := ∀ i, a i = 0 ∨ a i = 1

/-- Every derived polynomial vanishes on the common Boolean roots of the axioms. -/
theorem pcd_vanish {Ax : Set (MvPolynomial ℕ F)} {d : ℕ} {a : ℕ → F} (ha : BoolPt a)
    (hAx : ∀ f ∈ Ax, eval a f = 0) {f : MvPolynomial ℕ F} (h : PCD Ax d f) : eval a f = 0 := by
  induction h with
  | ax hf _ => exact hAx _ hf
  | bool i _ =>
    simp only [map_sub, map_pow, eval_X]
    rcases ha i with h | h <;> rw [h] <;> ring
  | lin a b _ _ ihf ihg => simp [ihf, ihg]
  | mul i _ _ ih => simp [ih]

/-- **Soundness**: a derivation of `1` rules out a common Boolean root. -/
theorem pcd_sound {Ax : Set (MvPolynomial ℕ F)} {d : ℕ} {a : ℕ → F} (ha : BoolPt a)
    (hAx : ∀ f ∈ Ax, eval a f = 0) : ¬ PCD Ax d 1 := by
  intro h
  have := pcd_vanish ha hAx h
  simp at this

/-! ## CNFs as polynomial systems -/

/-- The factor of a literal that vanishes exactly when the literal is true. -/
def litPoly (l : Literal) : MvPolynomial ℕ F := if l.pos then 1 - X l.var else X l.var

/-- A clause as the product of its literal factors. -/
def clausePoly (C : Clause) : MvPolynomial ℕ F := ∏ l ∈ C, litPoly l

/-- The polynomial system of a CNF. -/
def cnfAx (Φ : CNF) : Set (MvPolynomial ℕ F) := {f | ∃ C ∈ Φ, f = clausePoly C}

/-- The Boolean point of an assignment. -/
def boolPt (a : Assignment) : ℕ → F := fun i => if a i then 1 else 0

theorem boolPt_bool (a : Assignment) : BoolPt (F := F) (boolPt a) := by
  intro i; unfold boolPt; split_ifs <;> simp

theorem eval_litPoly {a : Assignment} {l : Literal} (h : litSat a l) :
    eval (boolPt (F := F) a) (litPoly l) = 0 := by
  unfold litPoly boolPt; unfold litSat at h
  cases hp : l.pos <;> simp [hp] at h ⊢ <;> simp [h]

theorem eval_clausePoly {a : Assignment} {C : Clause} (h : clauseSat a C) :
    eval (boolPt (F := F) a) (clausePoly C) = 0 := by
  obtain ⟨l, hl, hs⟩ := h
  unfold clausePoly
  rw [map_prod]
  exact Finset.prod_eq_zero hl (eval_litPoly hs)

/-- A CNF with a polynomial calculus refutation (of any degree) is unsatisfiable. -/
theorem pc_cnf_unsat {Φ : CNF} {d : ℕ} (h : PCD (cnfAx (F := F) Φ) d 1) : ¬ Satisfiable Φ := by
  rintro ⟨a, ha⟩
  refine pcd_sound (boolPt_bool a) ?_ h
  rintro f ⟨C, hC, rfl⟩
  exact eval_clausePoly (ha C hC)

end

end SATurday.ProofComplexity
