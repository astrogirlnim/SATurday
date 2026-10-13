import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Ordinary polynomial calculus foundations (R4 Phase 2.1, layer 2a)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`PolynomialCalculus.lean` (`Derives`, `degreeSpace`, `pcSpace`, `nsSpace`, `booleanBase`,
`unaryBase`, `functionalUnaryBase`, `compactBitBase`, `Derives.degree_le`, `Derives.mono`,
`nsSpace_generator`, ...), `PolynomialCalculusReuse.lean` (`Derives.mul_polynomial`,
`nsSpace_mul`, `nsSpace_le_pcSpace`), `PolynomialCalculusSubstitution.lean`
(`substitution_degree`, `Derives.substitute_weighted`, `Derives.substitute`),
`PolynomialCalculusDuality.lean` (`normalizedFunctional_iff`, `ns_design_iff`,
`pc_annihilator_iff`) together with the third party linear separation lemma it uses
(`LinearSeparation.normalized_annihilator_iff`).

This is *not* our `PCD` of `PolyCalc.lean`: it is over a field `K` with arbitrary variable type
`V`, hypotheses are charged their own degree, and the boolean axioms are an explicit base set
rather than a rule. Statements keep his quantifier shape.

LOG: R4 BraunPC module (Phase 2.1 layer 2a)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {K V : Type*} [Field K]

/-- Polynomials over `K` in the variables `V`. -/
abbrev Poly (K V : Type*) [Field K] := MvPolynomial V K

/-- Ordinary PC with degree ceiling `B` from the axiom set `F`. -/
inductive Derives (F : Set (Poly K V)) (B : ℕ) : Poly K V → Prop
  | zero : Derives F B 0
  | hyp {f} : f ∈ F → f.totalDegree ≤ B → Derives F B f
  | add {f g} : Derives F B f → Derives F B g → Derives F B (f + g)
  | smul (a : K) {f} : Derives F B f → Derives F B (a • f)
  | mul_var (v : V) {f} : Derives F B f → (X v * f).totalDegree ≤ B → Derives F B (X v * f)

theorem Derives.degree_le {F : Set (Poly K V)} {B : ℕ} {f : Poly K V}
    (h : Derives F B f) : f.totalDegree ≤ B := by
  induction h with
  | zero => simp
  | hyp _ h => exact h
  | add _ _ ih jh => exact (totalDegree_add _ _).trans (max_le ih jh)
  | smul a _ ih => exact (totalDegree_smul_le a _).trans ih
  | mul_var _ _ h _ => exact h

theorem Derives.mono {F G : Set (Poly K V)} {B C : ℕ} {f : Poly K V}
    (h : Derives F B f) (hFG : F ⊆ G) (hBC : B ≤ C) : Derives G C f := by
  induction h with
  | zero => exact .zero
  | hyp hf hd => exact .hyp (hFG hf) (hd.trans hBC)
  | add _ _ ih jh => exact .add ih jh
  | smul a _ ih => exact .smul a ih
  | mul_var v _ hd ih => exact .mul_var v ih (hd.trans hBC)

/-- Polynomials of total degree at most `B`. -/
def degreeSpace (B : ℕ) : Submodule K (Poly K V) where
  carrier := {f | f.totalDegree ≤ B}
  zero_mem' := by simp
  add_mem' := fun hf hg => (totalDegree_add _ _).trans (max_le hf hg)
  smul_mem' := fun a _ hf => (totalDegree_smul_le a _).trans hf

theorem degreeSpace_eq_restrictTotalDegree (B : ℕ) :
    degreeSpace (K := K) (V := V) B = restrictTotalDegree V K B := by
  ext f
  exact (mem_restrictTotalDegree V B f).symm

/-- The linear space of PC-derivable polynomials. -/
def pcSpace (F : Set (Poly K V)) (B : ℕ) : Submodule K (Poly K V) where
  carrier := {f | Derives F B f}
  zero_mem' := .zero
  add_mem' := .add
  smul_mem' := fun a _ h => .smul a h

@[simp] theorem mem_pcSpace (F : Set (Poly K V)) (B : ℕ) (f : Poly K V) :
    f ∈ pcSpace F B ↔ Derives F B f := Iff.rfl

/-- Degree truncated Nullstellensatz span: each axiom multiple is charged separately. -/
def nsSpace (F : Set (Poly K V)) (B : ℕ) : Submodule K (Poly K V) :=
  Submodule.span K {p | ∃ f ∈ F, ∃ q : Poly K V, p = q * f ∧ p.totalDegree ≤ B}

theorem nsSpace_le_degreeSpace (F : Set (Poly K V)) (B : ℕ) :
    nsSpace F B ≤ degreeSpace B :=
  Submodule.span_le.mpr (by rintro p ⟨f, _, q, _, hd⟩; exact hd)

theorem nsSpace_mono {F G : Set (Poly K V)} {B C : ℕ}
    (hFG : F ⊆ G) (hBC : B ≤ C) : nsSpace F B ≤ nsSpace G C :=
  Submodule.span_mono (by
    rintro p ⟨f, hf, q, heq, hd⟩
    exact ⟨f, hFG hf, q, heq, hd.trans hBC⟩)

theorem nsSpace_generator {F : Set (Poly K V)} {B : ℕ} {f q : Poly K V}
    (hf : f ∈ F) (hd : (q * f).totalDegree ≤ B) : q * f ∈ nsSpace F B :=
  Submodule.subset_span ⟨f, hf, q, rfl, hd⟩

/-- Boolean axioms `x^2 - x`. -/
def booleanBase : Set (Poly K V) := {f | ∃ v, f = X v ^ 2 - X v}

/-- Unary pigeonhole base: Boolean, row sums equal one, no two pigeons share a hole. -/
def unaryBase (m n : ℕ) : Set (Poly K (Fin m × Fin n)) :=
  booleanBase ∪ {f | ∃ i, f = (∑ j : Fin n, X (i, j)) - 1} ∪
    {f | ∃ i i' j, i ≠ i' ∧ f = X (i, j) * X (i', j)}

/-- Unary base plus functionality. -/
def functionalUnaryBase (m n : ℕ) : Set (Poly K (Fin m × Fin n)) :=
  unaryBase m n ∪ {f | ∃ i j j', j ≠ j' ∧ f = X (i, j) * X (i, j')}

/-- Compact binary encoding base over `F_2`: pigeons `i < i'` have distinct codes. -/
def compactBitBase (m ℓ : ℕ) : Set (Poly (ZMod 2) (Fin m × Fin ℓ)) :=
  booleanBase ∪ {f | ∃ i i' : Fin m, i < i' ∧ f = ∏ t : Fin ℓ, (1 + X (i, t) + X (i', t))}

/-! ### Reuse of completed lines -/

variable {F : Set (Poly K V)} {B : ℕ}

private theorem mul_monomial_line (f : Poly K V) (hf : Derives F B f) (s : V →₀ ℕ) (a : K) :
    Derives F (max B ((monomial s a).totalDegree + f.totalDegree)) (monomial s a * f) := by
  apply induction_on_monomial (motive := fun q : Poly K V =>
    Derives F (max B (q.totalDegree + f.totalDegree)) (q * f))
  · intro c
    simpa only [totalDegree_C, zero_add, C_mul'] using
      (Derives.smul c hf).mono (fun _ h => h) (le_max_left B f.totalDegree)
  · intro q v ih
    by_cases hq : q = 0
    · simp only [hq, zero_mul]
      exact .zero
    have hv : (X v : Poly K V) ≠ 0 := X_ne_zero v
    have hd : (q * X v).totalDegree = q.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hq hv, totalDegree_X]
    have hbound : (X v * (q * f)).totalDegree ≤
        max B ((q * X v).totalDegree + f.totalDegree) := by
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_X]
      apply (Nat.add_le_add_left (totalDegree_mul q f) 1).trans
      rw [hd]
      omega
    have hprev := ih.mono (fun _ h => h)
      (show max B (q.totalDegree + f.totalDegree) ≤
        max B ((q * X v).totalDegree + f.totalDegree) by rw [hd]; omega)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using Derives.mul_var v hprev hbound

/-- Multiplying a completed line by any polynomial: ceiling `max B (deg q + deg f)`. -/
theorem Derives.mul_polynomial {f : Poly K V} (hf : Derives F B f) (q : Poly K V) :
    Derives F (max B (q.totalDegree + f.totalDegree)) (q * f) := by
  classical
  have heq : q * f = ∑ s ∈ q.support, monomial s (q.coeff s) * f := by
    conv_lhs => rw [q.as_sum, Finset.sum_mul]
  rw [heq]
  change (∑ s ∈ q.support, monomial s (q.coeff s) * f) ∈
    pcSpace F (max B (q.totalDegree + f.totalDegree))
  apply Submodule.sum_mem
  intro s hs
  apply (mul_monomial_line f hf s (q.coeff s)).mono (fun _ h => h)
  apply max_le_max le_rfl
  exact Nat.add_le_add_right ((totalDegree_monomial_le s _).trans (le_totalDegree hs)) _

theorem nsSpace_mul {p : Poly K V} (hp : p ∈ nsSpace F B) (q : Poly K V) :
    q * p ∈ nsSpace F (B + q.totalDegree) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨f, hf, r, rfl, hd⟩
    rw [← mul_assoc]
    apply nsSpace_generator hf
    rw [mul_assoc]
    exact (totalDegree_mul _ _).trans (by omega)
  | zero => simp
  | add x y _ _ ih jh =>
    simpa only [mul_add] using (nsSpace F (B + q.totalDegree)).add_mem ih jh
  | smul a x _ ih =>
    simpa only [mul_smul_comm] using (nsSpace F (B + q.totalDegree)).smul_mem a ih

theorem nsSpace_le_pcSpace (F : Set (Poly K V)) (B : ℕ) : nsSpace F B ≤ pcSpace F B := by
  apply Submodule.span_le.mpr
  rintro p ⟨f, hf, q, rfl, hd⟩
  by_cases hz : q * f = 0
  · rw [hz]
    exact .zero
  have hq : q ≠ 0 := left_ne_zero_of_mul hz
  have hfn : f ≠ 0 := right_ne_zero_of_mul hz
  have heq := totalDegree_mul_of_isDomain hq hfn
  have hfd : f.totalDegree ≤ B := by omega
  exact ((Derives.hyp hf hfd).mul_polynomial q).mono (fun _ h => h) (by omega)

/-! ### Substitution -/

section Substitution

variable {W : Type*}

private theorem substitution_monomial_degree (g : V → Poly K W) (T : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ T) (s : V →₀ ℕ) (a : K) :
    (aeval g (monomial s a)).totalDegree ≤ T * s.sum (fun _ n => n) := by
  classical
  rw [aeval_monomial]
  apply (totalDegree_mul _ _).trans
  change (C a : Poly K W).totalDegree + _ ≤ _
  rw [totalDegree_C, zero_add, Finsupp.prod]
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ v ∈ s.support, T * s v := by
      refine Finset.sum_le_sum fun v _ => ?_
      exact (totalDegree_pow (g v) (s v)).trans
        (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (s v) (hg v))
    _ = T * s.sum (fun _ n => n) := by rw [Finsupp.sum, Finset.mul_sum]

/-- Substituting polynomials of degree at most `T` multiplies the degree by at most `T`. -/
theorem substitution_degree (g : V → Poly K W) (T : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ T) (f : Poly K V) :
    (aeval g f).totalDegree ≤ T * f.totalDegree := by
  classical
  have heq : aeval g f = ∑ s ∈ f.support, aeval g (monomial s (f.coeff s)) := by
    conv_lhs => rw [f.as_sum, map_sum]
  rw [heq]
  apply totalDegree_finsetSum_le
  intro s hs
  exact (substitution_monomial_degree g T hg s _).trans
    (Nat.mul_le_mul_left T (le_totalDegree hs))

theorem Derives.substitute_weighted {D : ℕ} {f : Poly K V}
    (hf : Derives F D f) (g : V → Poly K W) (T : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ T) (G : Set (Poly K W)) (weight : Poly K W)
    (haxioms : ∀ a ∈ F, a.totalDegree ≤ D →
      Derives G (T * D + weight.totalDegree) (weight * aeval g a)) :
    Derives G (T * D + weight.totalDegree) (weight * aeval g f) := by
  induction hf with
  | zero => simpa only [map_zero, mul_zero] using
      (Derives.zero : Derives G (T * D + weight.totalDegree) 0)
  | hyp ha hd => exact haxioms _ ha hd
  | add _ _ ih jh => simpa only [map_add, mul_add] using Derives.add ih jh
  | smul a _ ih => simpa only [map_smul, mul_smul_comm] using Derives.smul a ih
  | @mul_var v p hp hdp ih =>
    by_cases hz : p = 0
    · simp only [hz, mul_zero, map_zero]
      exact .zero
    have hpred : p.totalDegree + 1 ≤ D := by
      rwa [totalDegree_mul_of_isDomain (X_ne_zero v) hz, totalDegree_X, Nat.add_comm] at hdp
    have himage : (weight * aeval g p).totalDegree ≤
        weight.totalDegree + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_left (substitution_degree g T hg p) _)
    have hcost : (g v).totalDegree + (weight * aeval g p).totalDegree ≤
        T * D + weight.totalDegree := by
      have hgv := hg v
      have ht := Nat.mul_le_mul_left T hpred
      rw [Nat.mul_add, Nat.mul_one] at ht
      omega
    have hh := (ih.mul_polynomial (g v)).mono (fun _ h => h) (max_le le_rfl hcost)
    simpa only [map_mul, aeval_X, mul_assoc, mul_left_comm] using hh

theorem Derives.substitute {D : ℕ} {f : Poly K V}
    (hf : Derives F D f) (g : V → Poly K W) (T : ℕ)
    (hg : ∀ v, (g v).totalDegree ≤ T) :
    Derives ((aeval g) '' F) (T * D) (aeval g f) := by
  have h := hf.substitute_weighted g T hg ((aeval g) '' F) 1 (by
    intro a ha hd
    simp only [totalDegree_one, Nat.add_zero, one_mul]
    exact Derives.hyp ⟨a, ha, rfl⟩
      ((substitution_degree g T hg a).trans (Nat.mul_le_mul_left T hd)))
  simpa only [totalDegree_one, Nat.add_zero, one_mul] using h

end Substitution

/-! ### Finite dimensional separation -/

/-- Linear separation: a normalized functional annihilating `S` exists iff `v ∉ S`. -/
theorem normalized_annihilator_iff {M : Type*} [AddCommGroup M] [Module K M]
    (S : Submodule K M) (v : M) :
    (∃ l : M →ₗ[K] K, l v = 1 ∧ ∀ x ∈ S, l x = 0) ↔ v ∉ S := by
  constructor
  · rintro ⟨l, hl, hS⟩ hv
    exact one_ne_zero (hl.symm.trans (hS v hv))
  · intro hv
    obtain ⟨l, hS, hl⟩ := LinearMap.exists_extend_of_notMem (0 : S →ₗ[K] K) hv 1
    exact ⟨l, hl, fun x hx => LinearMap.congr_fun hS ⟨x, hx⟩⟩

/-- A normalized functional on the bounded degree space annihilating the eligible members of `S`. -/
def HasNormalizedFunctional (S : Submodule K (Poly K V)) (B : ℕ) : Prop :=
  ∃ l : degreeSpace (K := K) (V := V) B →ₗ[K] K,
    l ⟨1, by simp [degreeSpace]⟩ = 1 ∧
      ∀ p : degreeSpace (K := K) (V := V) B, (p : Poly K V) ∈ S → l p = 0

theorem normalizedFunctional_iff (S : Submodule K (Poly K V)) (B : ℕ) :
    HasNormalizedFunctional S B ↔ (1 : Poly K V) ∉ S :=
  normalized_annihilator_iff (M := degreeSpace (K := K) (V := V) B)
    (S.comap (degreeSpace B).subtype) ⟨1, by simp [degreeSpace]⟩

theorem ns_design_iff (F : Set (Poly K V)) (B : ℕ) :
    HasNormalizedFunctional (nsSpace F B) B ↔ (1 : Poly K V) ∉ nsSpace F B :=
  normalizedFunctional_iff _ _

theorem pc_annihilator_iff (F : Set (Poly K V)) (B : ℕ) :
    HasNormalizedFunctional (pcSpace F B) B ↔ ¬ Derives F B (1 : Poly K V) :=
  normalizedFunctional_iff _ _

end

end SATurday.ProofComplexity.BraunPC
