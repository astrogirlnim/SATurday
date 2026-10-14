import Theory.ProofComplexity.PolyCalc
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Candidate C1: the proof system `R_rho^p` of rank-bounded linear terms (definitions, soundness,
# term-to-polynomial translation)

See `docs/ladder/rungs/r4-phase23-c1.md` (Section 1) and `docs/ladder/rungs/r4-c1-lean-plan.md`.

* an affine form over `F_p = ZMod p` in the variables `ℕ` is a pair (finitely supported
  coefficient vector, constant); forms form an `F_p`-vector space;
* a term is a finite set of forms (read as the conjunction of the equations `l = 0`), its rank is
  the dimension of the span of its forms (constants included);
* a line is a finite set of terms (their disjunction), `ρ`-bounded when every term has rank `≤ ρ`;
* `RInfer` / `RRefutation` is the dag-like system with axioms, weakening and the semantic term
  rule `Sem` (semantic consequence on the Boolean cube); size = number of nodes;
* `chi T = ∏_{l ∈ B_T} (1 - l^(p-1))`, `B_T` a maximal independent subset of `T`: a polynomial of
  degree `≤ (p-1) rank T` that is the `0/1` indicator of the term (`eval_chi`).

What is NOT here (see the plan file): the simulation into `Res(PC_r/F_p)` with `r = 3(p-1)ρ`, which
needs a degree `r` version of the Pang system and of its lower bound (the formalised Pang theorem
is only `r = 1`), and the numeric chain with `κ`.
-/

open SATurday.ProofComplexity MvPolynomial

namespace C1

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- Affine forms `∑ c_i x_i + c_0` over `F_p`. -/
abbrev AffForm (p : ℕ) [Fact p.Prime] := (ℕ →₀ ZMod p) × ZMod p

/-- Value of a form at a point `a : ℕ → F_p`; an `F_p`-linear map in the form. -/
def ev (a : ℕ → ZMod p) : AffForm p →ₗ[ZMod p] ZMod p :=
  (Finsupp.linearCombination (ZMod p) a).coprod LinearMap.id

theorem ev_apply (a : ℕ → ZMod p) (l : AffForm p) :
    ev a l = l.1.sum (fun i c => c * a i) + l.2 := by
  simp [ev, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

/-- The polynomial of a form. -/
def formPoly (l : AffForm p) : MvPolynomial ℕ (ZMod p) :=
  l.1.sum (fun i c => C c * X i) + C l.2

theorem eval_formPoly (a : ℕ → ZMod p) (l : AffForm p) :
    MvPolynomial.eval a (formPoly l) = ev a l := by
  rw [ev_apply]
  simp [formPoly, Finsupp.sum, map_sum]

theorem totalDegree_formPoly (l : AffForm p) : (formPoly l).totalDegree ≤ 1 := by
  unfold formPoly Finsupp.sum
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_mul _ _).trans (by simp)

/-- A term: a finite set of forms (the conjunction of the equations `l = 0`). -/
abbrev Term (p : ℕ) [Fact p.Prime] := Finset (AffForm p)

/-- The rank of a term. -/
def rank (T : Term p) : ℕ := Module.finrank (ZMod p) (Submodule.span (ZMod p) (T : Set (AffForm p)))

/-- The term holds at the point `a`. -/
def TrueAt (a : ℕ → ZMod p) (T : Term p) : Prop := ∀ l ∈ T, ev a l = 0

/-- A line: a finite set of terms (their disjunction). -/
abbrev RLine (p : ℕ) [Fact p.Prime] := Finset (Term p)

/-- `ρ`-bounded line. -/
def Bdd (ρ : ℕ) (L : RLine p) : Prop := ∀ T ∈ L, rank T ≤ ρ

/-- The line holds at the point `a`. -/
def LTrue (a : ℕ → ZMod p) (L : RLine p) : Prop := ∃ T ∈ L, TrueAt a T

/-- Form `x_i` (as a term: the equation `x_i = 0`) and `x_i - 1`. -/
def formVar (i : ℕ) : AffForm p := (Finsupp.single i 1, 0)
def formVarSub (i : ℕ) : AffForm p := (Finsupp.single i 1, -1)

theorem ev_formVar (a : ℕ → ZMod p) (i : ℕ) : ev a (formVar i) = a i := by
  simp [ev_apply, formVar]

theorem ev_formVarSub (a : ℕ → ZMod p) (i : ℕ) : ev a (formVarSub i) = a i - 1 := by
  simp [ev_apply, formVarSub, sub_eq_add_neg]

/-- A literal as a rank-`1` term: the positive literal is true iff `x = 1`. -/
def litTerm (l : Literal) : Term p := if l.pos then {formVarSub l.var} else {formVar l.var}

/-- The line of a clause. -/
def clauseRLine (C : Clause) : RLine p := C.image litTerm

theorem LTrue_clauseRLine {a : Assignment} {C : Clause} (h : clauseSat a C) :
    LTrue (boolPt (F := ZMod p) a) (clauseRLine C) := by
  obtain ⟨l, hl, hs⟩ := h
  refine ⟨litTerm l, Finset.mem_image.2 ⟨l, hl, rfl⟩, ?_⟩
  unfold litSat at hs
  intro f hf
  unfold litTerm at hf
  by_cases hp : l.pos = true
  · simp only [hp, if_true, Finset.mem_singleton] at hf
    subst hf
    rw [ev_formVarSub]; unfold boolPt; rw [hs.trans hp]; simp
  · have hp' : l.pos = false := by simpa using hp
    simp only [hp', Bool.false_eq_true, if_false, Finset.mem_singleton] at hf
    subst hf
    rw [ev_formVar]; unfold boolPt; rw [hs.trans hp']; simp

/-- Semantic consequence on the Boolean cube: `T1 ∧ T2 ⊨ T3` (`T2 = none` means no second
premise, `T3 = none` means the empty conclusion, i.e. `T1 ∧ T2` is unsatisfiable on the cube). -/
def SemOK (T₁ : Term p) (T₂ T₃ : Option (Term p)) : Prop :=
  ∀ a : Assignment, TrueAt (boolPt (F := ZMod p) a) T₁ →
    (∀ T, T₂ = some T → TrueAt (boolPt (F := ZMod p) a) T) →
    ∃ T, T₃ = some T ∧ TrueAt (boolPt (F := ZMod p) a) T

/-- One inference step of `R_ρ^p`. -/
inductive RInfer (Φ : CNF) (ρ : ℕ) : List (RLine p) → RLine p → Prop
  | init (C : Clause) (hC : C ∈ Φ) : RInfer Φ ρ [] (clauseRLine C)
  | taut (i : ℕ) : RInfer Φ ρ [] {{formVar i}, {formVarSub i}}
  | weak {L : RLine p} (L' : RLine p) (h : L ⊆ L') : RInfer Φ ρ [L] L'
  /-- Semantic term rule with one premise `L₁ ∪ {T₁}` (simplification, weakening of a term,
  falsum from a single inconsistent term). -/
  | sem1 {L₁ : RLine p} {T₁ : Term p} {T₃ : Option (Term p)}
      (h₁ : T₁ ∈ L₁) (hs : SemOK T₁ none T₃) (L' : RLine p) (hL' : L₁.erase T₁ ⊆ L')
      (hT₃ : ∀ T, T₃ = some T → T ∈ L') (hb : ∀ T, T₃ = some T → rank T ≤ ρ) :
      RInfer Φ ρ [L₁] L'
  /-- Semantic term rule with two premises `L₁ ∪ {T₁}`, `L₂ ∪ {T₂}` (cut, resolution, AND
  introduction are special cases). -/
  | sem2 {L₁ L₂ : RLine p} {T₁ T₂ : Term p} {T₃ : Option (Term p)}
      (h₁ : T₁ ∈ L₁) (h₂ : T₂ ∈ L₂) (hs : SemOK T₁ (some T₂) T₃) (L' : RLine p)
      (hL₁ : L₁.erase T₁ ⊆ L') (hL₂ : L₂.erase T₂ ⊆ L')
      (hT₃ : ∀ T, T₃ = some T → T ∈ L') (hb : ∀ T, T₃ = some T → rank T ≤ ρ) :
      RInfer Φ ρ [L₁, L₂] L'

/-- Soundness of one step at a Boolean point. -/
theorem RInfer.sound {Φ : CNF} {ρ : ℕ} {a : Assignment} (ha : cnfSat a Φ)
    {Ls : List (RLine p)} {L : RLine p} (h : RInfer Φ ρ Ls L)
    (hL : ∀ M ∈ Ls, LTrue (boolPt (F := ZMod p) a) M) : LTrue (boolPt (F := ZMod p) a) L := by
  cases h with
  | init C hC => exact LTrue_clauseRLine (ha C hC)
  | taut i =>
    rcases boolPt_bool (F := ZMod p) a i with h0 | h1
    · refine ⟨{formVar i}, by simp, ?_⟩
      intro f hf; simp at hf; subst hf; rw [ev_formVar]; exact h0
    · refine ⟨{formVarSub i}, by simp, ?_⟩
      intro f hf; simp at hf; subst hf; rw [ev_formVarSub, h1]; simp
  | weak L' h =>
    obtain ⟨T, hT, hz⟩ := hL _ (List.mem_singleton_self _)
    exact ⟨T, h hT, hz⟩
  | @sem1 L₁ T₁ T₃ h₁ hs L' hL' hT₃ hb =>
    obtain ⟨T, hT, hz⟩ := hL L₁ (by simp)
    by_cases e : T = T₁
    · subst e
      obtain ⟨T3, h3, hz3⟩ := hs a hz (by simp)
      exact ⟨T3, hT₃ T3 h3, hz3⟩
    · exact ⟨T, hL' (Finset.mem_erase.2 ⟨e, hT⟩), hz⟩
  | @sem2 L₁ L₂ T₁ T₂ T₃ h₁ h₂ hs L' hL₁ hL₂ hT₃ hb =>
    obtain ⟨T, hT, hz⟩ := hL L₁ (by simp)
    obtain ⟨U, hU, hy⟩ := hL L₂ (by simp)
    by_cases e : T = T₁
    · by_cases e2 : U = T₂
      · subst e; subst e2
        obtain ⟨T3, h3, hz3⟩ := hs a hz (by intro V hV; cases hV; exact hy)
        exact ⟨T3, hT₃ T3 h3, hz3⟩
      · exact ⟨U, hL₂ (Finset.mem_erase.2 ⟨e2, hU⟩), hy⟩
    · exact ⟨T, hL₁ (Finset.mem_erase.2 ⟨e, hT⟩), hz⟩

/-- A dag-like refutation in `R_ρ^p`: nodes `0, …, S-1`, every line `ρ`-bounded, last line empty.
The size is the number of nodes `S`. -/
structure RRefutation (Φ : CNF) (ρ : ℕ) (p : ℕ) [Fact p.Prime] where
  S : ℕ
  line : ℕ → RLine p
  prem : ℕ → List ℕ
  S_pos : 0 < S
  prem_lt : ∀ i < S, ∀ j ∈ prem i, j < i
  infer : ∀ i < S, RInfer Φ ρ ((prem i).map line) (line i)
  bdd : ∀ i < S, Bdd ρ (line i)
  last : line (S - 1) = ∅

/-- **Soundness**: a satisfiable CNF has no refutation in `R_ρ^p`. -/
theorem RRefutation.unsat {Φ : CNF} {ρ : ℕ} (R : RRefutation Φ ρ p) : ¬ Satisfiable Φ := by
  rintro ⟨a, ha⟩
  have key : ∀ i < R.S, LTrue (boolPt (F := ZMod p) a) (R.line i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      refine RInfer.sound ha (R.infer i hi) ?_
      intro M hM
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hM
      exact ih j (R.prem_lt i hi j hj) ((R.prem_lt i hi j hj).trans hi)
  obtain ⟨T, hT, _⟩ := key (R.S - 1) (by have := R.S_pos; omega)
  rw [R.last] at hT
  simp at hT

/-! ### The translation `chi` -/

/-- A maximal linearly independent subset of a term (by choice). -/
def basisOf (T : Term p) : Finset (AffForm p) :=
  (T.finite_toSet.subset
    (Classical.choose_spec (exists_linearIndependent (ZMod p) (T : Set (AffForm p)))).1 : Set.Finite
      (Classical.choose (exists_linearIndependent (ZMod p) (T : Set (AffForm p))))).toFinset

theorem basisOf_spec (T : Term p) :
    ((basisOf T : Finset (AffForm p)) : Set (AffForm p)) ⊆ T ∧
    Submodule.span (ZMod p) ((basisOf T : Finset (AffForm p)) : Set (AffForm p)) =
      Submodule.span (ZMod p) (T : Set (AffForm p)) ∧
    LinearIndepOn (ZMod p) id ((basisOf T : Finset (AffForm p)) : Set (AffForm p)) := by
  have h := Classical.choose_spec (exists_linearIndependent (ZMod p) (T : Set (AffForm p)))
  have e : ((basisOf T : Finset (AffForm p)) : Set (AffForm p)) =
      Classical.choose (exists_linearIndependent (ZMod p) (T : Set (AffForm p))) := by
    unfold basisOf; simp
  rw [e]
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem card_basisOf (T : Term p) : (basisOf T).card = rank T := by
  obtain ⟨_, hspan, hli⟩ := basisOf_spec T
  unfold rank
  rw [← hspan]
  have := finrank_span_finset_eq_card (R := ZMod p) (s := basisOf T) (by simpa using hli)
  exact this.symm

/-- The polynomial translation of a term: `∏_{l ∈ B_T} (1 - l^(p-1))`. -/
def chi (T : Term p) : MvPolynomial ℕ (ZMod p) :=
  ∏ l ∈ basisOf T, (1 - formPoly l ^ (p - 1))

theorem eval_chi (a : ℕ → ZMod p) (T : Term p) :
    MvPolynomial.eval a (chi T) = if TrueAt a T then 1 else 0 := by
  obtain ⟨hsub, hspan, _⟩ := basisOf_spec T
  have key : TrueAt a T ↔ ∀ l ∈ basisOf T, ev a l = 0 := by
    constructor
    · intro h l hl; exact h l (hsub hl)
    · intro h l hl
      have : l ∈ Submodule.span (ZMod p) ((basisOf T : Finset (AffForm p)) : Set (AffForm p)) := by
        rw [hspan]; exact Submodule.subset_span hl
      have hle : Submodule.span (ZMod p) ((basisOf T : Finset (AffForm p)) : Set (AffForm p)) ≤
          LinearMap.ker (ev a) := by
        rw [Submodule.span_le]; intro x hx; exact h x hx
      exact hle this
  unfold chi
  rw [map_prod]
  by_cases hT : TrueAt a T
  · rw [if_pos hT]
    refine Finset.prod_eq_one fun l hl => ?_
    rw [map_sub, map_pow, eval_formPoly, (key.1 hT) l hl]
    simp [zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)]
  · rw [if_neg hT]
    have : ∃ l ∈ basisOf T, ev a l ≠ 0 := by
      by_contra hc; push Not at hc; exact hT (key.2 hc)
    obtain ⟨l, hl, hne⟩ := this
    refine Finset.prod_eq_zero hl ?_
    rw [map_sub, map_pow, eval_formPoly, ZMod.pow_card_sub_one_eq_one hne]
    simp

theorem totalDegree_chi (T : Term p) : (chi T).totalDegree ≤ (p - 1) * rank T := by
  unfold chi
  refine (totalDegree_finset_prod _ _).trans ?_
  have : ∀ l ∈ basisOf T, (1 - formPoly l ^ (p - 1)).totalDegree ≤ p - 1 := by
    intro l _
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    exact (totalDegree_pow _ _).trans (by
      calc (p - 1) * (formPoly l).totalDegree ≤ (p - 1) * 1 :=
            Nat.mul_le_mul_left _ (totalDegree_formPoly l)
        _ = p - 1 := mul_one _)
  calc ∑ l ∈ basisOf T, (1 - formPoly l ^ (p - 1)).totalDegree ≤ ∑ _l ∈ basisOf T, (p - 1) :=
        Finset.sum_le_sum this
    _ = (p - 1) * rank T := by rw [Finset.sum_const, card_basisOf, smul_eq_mul, mul_comm]

/-- Soundness of the translation of a line: the clause `∨_T (chi T - 1 = 0)` holds at `a`
exactly when the line holds. -/
theorem LTrue_iff_chi (a : ℕ → ZMod p) (L : RLine p) :
    LTrue a L ↔ ∃ T ∈ L, MvPolynomial.eval a (chi T - 1) = 0 := by
  unfold LTrue
  refine exists_congr fun T => and_congr_right fun _ => ?_
  rw [map_sub, eval_chi, map_one]
  by_cases h : TrueAt a T
  · simp [h]
  · simp [h]

end

end C1
