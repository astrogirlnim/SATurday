import Theory.ProofComplexity.BraunPC
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Tactic.FinCases

/-!
# Boolean reduction over `F_2` and the MP telescoping identity (R4 Phase 2.1, layer 2b)

Credit. Port of K. Braun (arXiv 2609.23015, author's Lean development):
`BooleanReduction.lean` (`supportMonomial`, `squarefreePart` and their degree, restricted,
evaluation lemmas, `squarefreePart_ns`, `boolean_vanishing_ns`, `boolean_vanishing_ns_bound`,
`polynomial_boolean_ns`, `polynomial_boolean_ns_bound`; here `sqMonomial`, `sqPart`) and
`MpTelescoping.lean` (`mp_telescoping`, `mp_coefficient_degree`, `mp_companion_degree`,
`mp_companion_equality_counterexample`). Statements keep his quantifier shape; proofs were
re-checked against our Mathlib and adapted where lemma names differ.

* Every polynomial over `F_2` is congruent to its squarefree part modulo the Boolean axioms at
  its own total degree (an ordinary NS witness), and a polynomial vanishing on all Boolean points
  of a finite variable type lies in `nsSpace booleanBase` at its own degree.
* The telescoping identity `1 - prod (1 - sum r f) = sum c f` with joint degree bounds.

LOG: R4 BraunPCBoolean module (Phase 2.1 layer 2b)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open scoped BigOperators
open MvPolynomial

section Boolean

variable {V : Type} [DecidableEq V]

/-- The multilinear monomial on a finite support. -/
def sqMonomial (S : Finset V) : MvPolynomial V (ZMod 2) := ∏ i ∈ S, X i

def sqPart (P : MvPolynomial V (ZMod 2)) : MvPolynomial V (ZMod 2) :=
  ∑ d ∈ P.support, P.coeff d • sqMonomial d.support

omit [DecidableEq V] in
theorem sqMonomial_degree (S : Finset V) : (sqMonomial S).totalDegree ≤ S.card := by
  simpa [sqMonomial] using totalDegree_finset_prod S (fun i => (X i : MvPolynomial V (ZMod 2)))

theorem sqMonomial_restricted (S : Finset V) :
    sqMonomial S ∈ restrictDegree V (ZMod 2) 1 := by
  rw [mem_restrictDegree_iff_sup]
  intro i
  rw [← degreeOf_def]
  have h := degreeOf_prod_le i S (fun j => (X j : MvPolynomial V (ZMod 2)))
  by_cases hi : i ∈ S
  · simpa [sqMonomial, degreeOf_X, hi] using h
  · exact (by simpa [sqMonomial, degreeOf_X, hi] using h :
      (sqMonomial S).degreeOf i ≤ 0).trans (by decide)

omit [DecidableEq V] in
private theorem support_card_le_sum (d : V →₀ ℕ) : d.support.card ≤ d.sum (fun _ n => n) := by
  classical
  change d.support.card ≤ ∑ i ∈ d.support, d i
  calc
    d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hi))

omit [DecidableEq V] in
theorem sqPart_degree (P : MvPolynomial V (ZMod 2)) :
    (sqPart P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_smul_le _ _).trans
  apply (sqMonomial_degree _).trans
  apply (support_card_le_sum d).trans
  exact le_totalDegree hd

theorem sqPart_restricted (P : MvPolynomial V (ZMod 2)) :
    sqPart P ∈ restrictDegree V (ZMod 2) 1 := by
  apply Submodule.sum_mem
  intro d _
  exact Submodule.smul_mem _ _ (sqMonomial_restricted _)

private theorem binary_pow (x : ZMod 2) (n : ℕ) (hn : n ≠ 0) : x^n = x := by
  fin_cases x
  · exact zero_pow hn
  · exact one_pow n

omit [DecidableEq V] in
theorem sqPart_eval (P : MvPolynomial V (ZMod 2)) (v : V → ZMod 2) :
    eval v (sqPart P) = eval v P := by
  classical
  conv_rhs => rw [P.as_sum]
  simp only [sqPart, map_sum, smul_eval]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_eq]
  simp only [map_mul, eval_C, sqMonomial, Finsupp.prod, eval_prod, eval_X, eval_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (binary_pow (v i) (d i) (Finsupp.mem_support_iff.mp hi)).symm

theorem sqPart_eq_zero_of_eval_zero [Fintype V] (P : MvPolynomial V (ZMod 2))
    (hP : ∀ v : V → ZMod 2, eval v P = 0) : sqPart P = 0 := by
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2)
  · intro v
    rw [sqPart_eval, hP]
  · simpa using sqPart_restricted P
omit [DecidableEq V] in
private theorem variable_power_reduction (i : V) (n : ℕ) :
    (X i : Poly (ZMod 2) V)^(n+1) - X i ∈ nsSpace booleanBase (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg : (X i : Poly (ZMod 2) V)^n * (X i^2-X i) ∈ nsSpace booleanBase (n+2) := by
      apply nsSpace_generator (F := booleanBase)
        (f := (X i : Poly (ZMod 2) V)^2-X i) (q := X i^n)
        (by exact ⟨i,rfl⟩)
      apply (totalDegree_mul _ _).trans
      have hpow := totalDegree_pow (X i : Poly (ZMod 2) V) 2
      have hsub := totalDegree_sub (X i^2 : Poly (ZMod 2) V) (X i)
      simp only [totalDegree_X_pow, totalDegree_X] at *
      omega
    have hi : (X i : Poly (ZMod 2) V)^(n+1)-X i ∈ nsSpace booleanBase (n+2) :=
      nsSpace_mono (Set.Subset.refl _) (by omega) ih
    have he : (X i : Poly (ZMod 2) V)^(n+1+1)-X i =
        X i^n*(X i^2-X i)+(X i^(n+1)-X i) := by
      simp only [pow_succ]
      ring
    rw [he]
    exact Submodule.add_mem _ hg hi
private theorem product_power_reduction (S : Finset V) (d : V → ℕ)
    (hd : ∀ i ∈ S, 1 ≤ d i) :
    (∏ i ∈ S, (X i : Poly (ZMod 2) V)^(d i)) - sqMonomial S ∈
      nsSpace booleanBase (∑ i ∈ S, d i) := by
  classical
  revert hd
  induction S using Finset.induction_on with
  | empty => intro _; simp [sqMonomial]
  | @insert i S hi ih =>
    intro hd
    have hdS : ∀ j ∈ S, 1 ≤ d j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hdi := hd i (Finset.mem_insert_self _ _)
    have hvar : (X i : Poly (ZMod 2) V)^(d i)-X i ∈ nsSpace booleanBase (d i) := by
      simpa [Nat.sub_add_cancel hdi] using variable_power_reduction i (d i-1)
    have hfirst : (X i : Poly (ZMod 2) V)^(d i) *
        ((∏ j ∈ S, (X j : Poly (ZMod 2) V)^(d j))-sqMonomial S) ∈
        nsSpace booleanBase (d i + ∑ j ∈ S, d j) := by
      exact nsSpace_mono (Set.Subset.refl _) (by simp [totalDegree_X_pow, Nat.add_comm])
        (nsSpace_mul (ih hdS) (X i^(d i)))
    have hcard : S.card ≤ ∑ j ∈ S, d j := by
      calc
        S.card = ∑ _j ∈ S, 1 := by simp
        _ ≤ ∑ j ∈ S, d j := Finset.sum_le_sum hdS
    have hsecond : sqMonomial S * ((X i : Poly (ZMod 2) V)^(d i)-X i) ∈
        nsSpace booleanBase (d i + ∑ j ∈ S, d j) :=
      nsSpace_mono (Set.Subset.refl _) (Nat.add_le_add_left
        ((sqMonomial_degree S).trans hcard) _) (nsSpace_mul hvar (sqMonomial S))
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have he : (X i : Poly (ZMod 2) V)^(d i) *
        (∏ j ∈ S, (X j : Poly (ZMod 2) V)^(d j)) - sqMonomial (insert i S) =
        X i^(d i)*((∏ j ∈ S, (X j : Poly (ZMod 2) V)^(d j))-sqMonomial S) +
          sqMonomial S*(X i^(d i)-X i) := by
      rw [sqMonomial, Finset.prod_insert hi]
      change _ - X i * sqMonomial S = _
      ring
    rw [he]
    exact Submodule.add_mem _ hfirst hsecond

private theorem monomial_reduction (d : V →₀ ℕ) :
    monomial d (1 : ZMod 2) - sqMonomial d.support ∈
      nsSpace booleanBase (d.sum (fun _ n => n)) := by
  rw [monomial_eq, C_1, one_mul]
  exact product_power_reduction d.support d
    (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem sqPart_ns (P : Poly (ZMod 2) V) :
    P-sqPart P ∈ nsSpace booleanBase P.totalDegree := by
  classical
  have he : P-sqPart P = ∑ d ∈ P.support,
      P.coeff d • (monomial d (1 : ZMod 2)-sqMonomial d.support) := by
    conv_lhs => lhs; rw [P.as_sum]
    rw [sqPart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    simp [smul_sub, smul_eq_C_mul, C_mul_monomial]
  rw [he]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  exact nsSpace_mono (Set.Subset.refl _) (le_totalDegree hd) (monomial_reduction d)

theorem boolean_vanishing_ns [Fintype V] (P : Poly (ZMod 2) V)
    (hP : ∀ v : V → ZMod 2, eval v P = 0) : P ∈ nsSpace booleanBase P.totalDegree := by
  simpa [sqPart_eq_zero_of_eval_zero P hP] using sqPart_ns P

theorem boolean_vanishing_ns_bound [Fintype V] (P : Poly (ZMod 2) V) (d : ℕ)
    (hd : P.totalDegree ≤ d) (hP : ∀ v : V → ZMod 2, eval v P = 0) :
    P ∈ nsSpace booleanBase d := nsSpace_mono (Set.Subset.refl _) hd (boolean_vanishing_ns P hP)

theorem polynomial_boolean_ns [Fintype V] (q : Poly (ZMod 2) V) :
    q^2-q ∈ nsSpace booleanBase (2*q.totalDegree) := by
  apply boolean_vanishing_ns_bound
  · exact (totalDegree_sub _ _).trans (max_le (totalDegree_pow q 2) (by omega))
  · intro v
    simp only [map_sub, map_pow]
    have h : eval v q ^ 2 = eval v q := ZMod.pow_card _
    rw [h, sub_self]

theorem sqPart_ns_bound (P : Poly (ZMod 2) V) (d : ℕ) (hd : P.totalDegree ≤ d) :
    P-sqPart P ∈ nsSpace booleanBase d :=
  nsSpace_mono (Set.Subset.refl _) hd (sqPart_ns P)

theorem polynomial_boolean_ns_bound [Fintype V] (q : Poly (ZMod 2) V) (k : ℕ)
    (hk : q.totalDegree ≤ k) : q^2-q ∈ nsSpace booleanBase (2*k) :=
  nsSpace_mono (Set.Subset.refl _) (Nat.mul_le_mul_left 2 hk) (polynomial_boolean_ns q)

end Boolean

section MP

variable {R ι σ : Type*} [CommRing R] [Fintype ι]

def ensProduct (f : ι → R) (r : ℕ → ι → R) (h : ℕ) : R :=
  ∏ v ∈ Finset.range h, (1 - ∑ i, r v i * f i)

def ensCoefficient (f : ι → R) (r : ℕ → ι → R) (h : ℕ) (i : ι) : R :=
  ∑ v ∈ Finset.range h, r v i * ensProduct f r v

theorem mp_telescoping (f : ι → R) (r : ℕ → ι → R) (h : ℕ) :
    1 - ensProduct f r h = ∑ i, ensCoefficient f r h i * f i := by
  induction h with
  | zero => simp [ensProduct, ensCoefficient]
  | succ h ih =>
    have hp : ensProduct f r (h + 1) =
        ensProduct f r h * (1 - ∑ i, r h i * f i) := by
      simp only [ensProduct, Finset.prod_range_succ]
    have hc (i : ι) : ensCoefficient f r (h + 1) i =
        ensCoefficient f r h i + r h i * ensProduct f r h := by
      simp only [ensCoefficient, Finset.sum_range_succ]
    simp_rw [hc, add_mul]
    rw [Finset.sum_add_distrib, ← ih, hp]
    have hs : (∑ i, r h i * ensProduct f r h * f i) =
        ensProduct f r h * ∑ i, r h i * f i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring

variable (f : ι → MvPolynomial σ R) (r : ℕ → ι → MvPolynomial σ R)
variable (δ h : ℕ)

lemma ensProduct_degree
    (hf : ∀ i, (f i).totalDegree ≤ δ)
    (hr : ∀ v < h, ∀ i, (r v i).totalDegree ≤ 1) :
    (ensProduct f r h).totalDegree ≤ h * (δ + 1) := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _v ∈ Finset.range h, (δ + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      apply (totalDegree_sub _ _).trans
      apply max_le
      · simp
      · apply totalDegree_finsetSum_le
        intro i _
        exact (totalDegree_mul _ _).trans (by
          simpa [Nat.add_comm] using Nat.add_le_add (hr v (Finset.mem_range.mp hv) i) (hf i))
    _ = h * (δ + 1) := by simp

theorem mp_coefficient_degree (i : ι)
    (hf : ∀ j, (f j).totalDegree ≤ δ)
    (hr : ∀ v < h, ∀ j, (r v j).totalDegree ≤ 1) :
    (ensCoefficient f r h i).totalDegree ≤ 1 + (h - 1) * (δ + 1) := by
  apply totalDegree_finsetSum_le
  intro v hv
  have vh : v < h := Finset.mem_range.mp hv
  have hd := ensProduct_degree f r δ v hf (fun w hw j => hr w (lt_trans hw vh) j)
  apply (totalDegree_mul _ _).trans
  exact (Nat.add_le_add (hr v vh i) hd).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right (δ + 1) (by omega : v ≤ h - 1)) 1)

theorem mp_companion_degree (i : ι)
    (hf : ∀ j, (f j).totalDegree ≤ δ)
    (hr : ∀ v < h, ∀ j, (r v j).totalDegree ≤ 1) :
    (f i * ensProduct f r h).totalDegree ≤ (f i).totalDegree + h * (δ + 1) := by
  exact (totalDegree_mul _ _).trans
    (Nat.add_le_add_left (ensProduct_degree f r δ h hf hr) _)

/- With h = 1, one constant input f = 1, and the legitimate loose bound δ = 1,
the source's proposed degree equality would give 2 instead of at most 1. -/
theorem mp_companion_equality_counterexample [Nontrivial R] :
    let f : Fin 1 → MvPolynomial (Fin 1) R := fun _ => 1
    let r : ℕ → Fin 1 → MvPolynomial (Fin 1) R := fun _ _ => X 0
    (∀ i, (f i).totalDegree ≤ 1) ∧
    (∀ v < 1, ∀ i, (r v i).totalDegree ≤ 1) ∧
    (f 0 * ensProduct f r 1).totalDegree ≠ (f 0).totalDegree + 1 * (1 + 1) := by
  dsimp
  refine ⟨by simp, by simp, ?_⟩
  have bound := mp_companion_degree
    (fun _ : Fin 1 => (1 : MvPolynomial (Fin 1) R))
    (fun (_ : ℕ) (_ : Fin 1) => (X 0 : MvPolynomial (Fin 1) R)) 0 1 0
    (by simp) (by simp)
  simp only [totalDegree_one, zero_add, zero_add, mul_one, zero_add] at bound ⊢
  omega


end MP

end

end SATurday.ProofComplexity.BraunPC
