import Theory.ProofComplexity.PolyCalc
import Mathlib.FieldTheory.Finite.Basic
/-!
# Pang route, layer A: dag-like `Res(lin F_p)` with syntactic rules

Lines are finite sets of linear (degree `≤ 1`) equations `h = 0` over `F_p` in the variables `V`
(a finite set of variable indices).  The rules are the syntactic ones of Pang (Section 1):
axioms `(0 = 0)`, `(x_i = 0) ∨ (x_i - 1 = 0)` and the clauses of the input CNF, weakening, deletion
of a false constant equation, linear combination `A ∨ (f=0), B ∨ (g=0) ⊢ A ∨ B ∨ (αf+βg=0)` and
multiplication `A ∨ (f=0) ⊢ A ∨ (fg=0)` (all polynomials of degree `≤ 1`).  Contraction is built
into the use of finite sets.  Linear combination, multiplication and false-constant deletion are
stated with a superset conclusion (weakening fused into the step, as in Pang's remark that many
disjuncts can be added in one step).  A refutation is a list of nodes (a dag, premises are
earlier nodes); its size is the number of nodes.  Semantic weakening is NOT included.

Differences from the paper, recorded honestly: no extension variables (all variables are in `V`);
the fused weakening above makes this system at least as strong as Pang's, so a lower bound for it
implies Pang's.
-/

open SATurday.ProofComplexity MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- Polynomials over `F_p` in variables indexed by `ℕ`. -/
abbrev Poly (p : ℕ) [Fact p.Prime] := MvPolynomial ℕ (ZMod p)

/-- A line: a finite disjunction of equations `h = 0`, recorded as the finite set of the `h`. -/
abbrev Line (p : ℕ) [Fact p.Prime] := Finset (Poly p)

/-- The line of a clause: `litPoly l = 0` says that the literal `l` is true. -/
def clauseLine (C : Clause) : Line p := C.image fun l => (litPoly l : Poly p)

/-- All equations are linear polynomials in the variables `V`. -/
def WF (V : Finset ℕ) (L : Line p) : Prop := ∀ h ∈ L, h.totalDegree ≤ 1 ∧ ∀ v ∈ h.vars, v ∈ V

/-- One syntactic inference step: premises, conclusion. -/
inductive Infer (Φ : CNF) (V : Finset ℕ) : List (Line p) → Line p → Prop
  | init (C : Clause) (hC : C ∈ Φ) : Infer Φ V [] (clauseLine C)
  | zero : Infer Φ V [] {0}
  | bool (i : ℕ) (hi : i ∈ V) : Infer Φ V [] {X i, X i - 1}
  | weak {L : Line p} (L' : Line p) (h : L ⊆ L') : Infer Φ V [L] L'
  | falseConst {L : Line p} (c : ZMod p) (hc : c ≠ 0) (hmem : (C c : Poly p) ∈ L) (L' : Line p)
      (h : L.erase (C c) ⊆ L') : Infer Φ V [L] L'
  | comb {L₁ L₂ : Line p} {f g : Poly p} (hf : f ∈ L₁) (hg : g ∈ L₂) (a b : ZMod p) (L' : Line p)
      (h : insert (C a * f + C b * g) (L₁.erase f ∪ L₂.erase g) ⊆ L') :
      Infer Φ V [L₁, L₂] L'
  | mul {L : Line p} {f : Poly p} (hf : f ∈ L) (g : Poly p) (hdeg : (f * g).totalDegree ≤ 1)
      (hvars : ∀ v ∈ g.vars, v ∈ V) (L' : Line p) (h : insert (f * g) (L.erase f) ⊆ L') :
      Infer Φ V [L] L'

/-- A dag-like refutation: nodes `0, …, S-1`, node `i` is inferred from the earlier nodes `prem i`;
the last node is the empty line. -/
structure Refutation (Φ : CNF) (V : Finset ℕ) (p : ℕ) [Fact p.Prime] where
  S : ℕ
  line : ℕ → Line p
  prem : ℕ → List ℕ
  S_pos : 0 < S
  prem_lt : ∀ i < S, ∀ j ∈ prem i, j < i
  infer : ∀ i < S, Infer Φ V ((prem i).map line) (line i)
  wf : ∀ i < S, WF V (line i)
  last : line (S - 1) = ∅

/-- Soundness of one step at a Boolean point. -/
theorem Infer.sound {Φ : CNF} {V : Finset ℕ} {a : Assignment} (ha : cnfSat a Φ)
    {Ls : List (Line p)} {L : Line p} (h : Infer Φ V Ls L)
    (hL : ∀ M ∈ Ls, ∃ q ∈ M, eval (boolPt (F := ZMod p) a) q = 0) :
    ∃ q ∈ L, eval (boolPt (F := ZMod p) a) q = 0 := by
  cases h with
  | init C hC =>
    obtain ⟨l, hl, hs⟩ := ha C hC
    exact ⟨litPoly l, Finset.mem_image.2 ⟨l, hl, rfl⟩, eval_litPoly hs⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | bool i _ =>
    have := boolPt_bool (F := ZMod p) a i
    rcases this with h | h
    · exact ⟨X i, by simp, by simp [h]⟩
    · exact ⟨X i - 1, by simp, by simp [h]⟩
  | weak L' h =>
    obtain ⟨q, hq, hz⟩ := hL _ (List.mem_singleton_self _)
    exact ⟨q, h hq, hz⟩
  | @falseConst L c hc hmem L' h =>
    obtain ⟨q, hq, hz⟩ := hL _ (List.mem_singleton_self _)
    refine ⟨q, h (Finset.mem_erase.2 ⟨?_, hq⟩), hz⟩
    rintro rfl
    simp at hz; exact hc hz
  | @comb L₁ L₂ f g hf hg α β L' h =>
    obtain ⟨q₁, hq₁, hz₁⟩ := hL L₁ (by simp)
    obtain ⟨q₂, hq₂, hz₂⟩ := hL L₂ (by simp)
    by_cases h1 : q₁ = f
    · by_cases h2 : q₂ = g
      · rw [h1] at hz₁; rw [h2] at hz₂
        exact ⟨C α * f + C β * g, h (Finset.mem_insert_self _ _), by simp [hz₁, hz₂]⟩
      · exact ⟨q₂, h (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨h2, hq₂⟩))), hz₂⟩
    · exact ⟨q₁, h (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨h1, hq₁⟩))), hz₁⟩
  | @mul L f hf g hdeg hvars L' h =>
    obtain ⟨q, hq, hz⟩ := hL _ (List.mem_singleton_self _)
    by_cases h1 : q = f
    · rw [h1] at hz
      exact ⟨f * g, h (Finset.mem_insert_self _ _), by simp [hz]⟩
    · exact ⟨q, h (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h1, hq⟩)), hz⟩

/-- **Soundness**: a satisfiable CNF has no refutation. -/
theorem Refutation.unsat {Φ : CNF} {V : Finset ℕ} (R : Refutation Φ V p) : ¬ Satisfiable Φ := by
  rintro ⟨a, ha⟩
  have key : ∀ i < R.S, ∃ q ∈ R.line i, eval (boolPt (F := ZMod p) a) q = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      refine Infer.sound ha (R.infer i hi) ?_
      intro M hM
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hM
      exact ih j (R.prem_lt i hi j hj) ((R.prem_lt i hi j hj).trans hi)
  obtain ⟨q, hq, _⟩ := key (R.S - 1) (by have := R.S_pos; omega)
  rw [R.last] at hq
  simp at hq

end

end Pang
