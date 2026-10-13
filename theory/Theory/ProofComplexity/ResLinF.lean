import Mathlib.Algebra.MvPolynomial.Basic
import Theory.ProofComplexity.PolyCalc

/-!
# Tree-like resolution over linear equations over a field (Ladder Rung R4, Phase 2.2, layer 1)

`Res(lin F)` of Raz and Tzameret, in the formulation of Part and Tzameret (arXiv 1806.09383):
lines are disjunctions of linear equations `∑ c_i x_i = a` over a field `F` in Boolean variables.
Here only the tree-like version is set up (`RLD`, indexed by width bound and number of leaves),
with the rules axiom, Boolean axiom, weakening, linear combination of two lines (the
"resolution" rule `C ∨ f = a`, `D ∨ g = b` ⊢ `C ∨ D ∨ αf+βg = αa+βb`) and simplification of
`0 = 1`.

Deviation from the paper: the combination rule carries the side condition that the new equation
does not already occur in the side clauses (see `docs/ladder/rungs/r4-phase22-plan.md`). Soundness
over Boolean points is `rld_sound`.

LOG: R4 Phase 2.2 ResLinF module (Res(lin F) definitions)
-/

namespace SATurday.ProofComplexity

namespace RLF

open MvPolynomial
open scoped Classical

noncomputable section

variable {F : Type} [Field F]

/-- A linear equation `∑ c_i x_i = a` over `F`. -/
abbrev LEq (F : Type) [Field F] := (ℕ →₀ F) × F

/-- Value of a linear form at a point. -/
def lval (c : ℕ →₀ F) (x : ℕ → F) : F := c.sum fun i a => a * x i

/-- The equation holds at `x`. -/
def eSat (x : ℕ → F) (e : LEq F) : Prop := lval e.1 x = e.2

/-- A linear clause (disjunction of equations) holds at `x`. -/
def clSat (x : ℕ → F) (L : Finset (LEq F)) : Prop := ∃ e ∈ L, eSat x e

theorem lval_add (c d : ℕ →₀ F) (x : ℕ → F) : lval (c + d) x = lval c x + lval d x := by
  unfold lval
  exact Finsupp.sum_add_index' (fun i => zero_mul _) (fun i a b => add_mul a b _)

theorem lval_smul (α : F) (c : ℕ →₀ F) (x : ℕ → F) : lval (α • c) x = α * lval c x := by
  unfold lval
  rw [Finsupp.sum_smul_index' (fun i => zero_mul _), Finsupp.mul_sum]
  simp [mul_assoc]

theorem lval_single (i : ℕ) (x : ℕ → F) : lval (Finsupp.single i (1 : F)) x = x i := by
  unfold lval
  rw [Finsupp.sum_single_index (zero_mul _)]; simp

theorem lval_zero (x : ℕ → F) : lval (0 : ℕ →₀ F) x = 0 := by simp [lval]

/-- Tree-like `Res(lin F)` derivations from the clause set `Ax`: `RLD Ax w L s` says `L` has a
derivation with `s` leaves in which every line has at most `w` equations. -/
inductive RLD (Ax : Set (Finset (LEq F))) (w : ℕ) : Finset (LEq F) → ℕ → Prop
  | ax {C} : C ∈ Ax → C.card ≤ w → RLD Ax w C 1
  | bool (i : ℕ) : 2 ≤ w →
      RLD Ax w {(Finsupp.single i (1 : F), 0), (Finsupp.single i (1 : F), 1)} 1
  | weak {L L' s} : RLD Ax w L s → L ⊆ L' → L'.card ≤ w → RLD Ax w L' s
  | comb {A B : Finset (LEq F)} {s1 s2 : ℕ} (e1 e2 : LEq F) (α β : F) :
      RLD Ax w A s1 → RLD Ax w B s2 → e1 ∈ A → e2 ∈ B →
      (α • e1.1 + β • e2.1, α * e1.2 + β * e2.2) ∉ A.erase e1 ∪ B.erase e2 →
      (A.erase e1 ∪ B.erase e2 ∪ {(α • e1.1 + β • e2.1, α * e1.2 + β * e2.2)}).card ≤ w →
      RLD Ax w (A.erase e1 ∪ B.erase e2 ∪ {(α • e1.1 + β • e2.1, α * e1.2 + β * e2.2)}) (s1 + s2)
  | simp {L s} : RLD Ax w (insert ((0 : ℕ →₀ F), (1 : F)) L) s → RLD Ax w L s

/-- **Soundness**: a derivation holds at every Boolean point satisfying the axioms. -/
theorem rld_sound {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s : ℕ}
    (h : RLD Ax w L s) {x : ℕ → F} (hx : BoolPt x) (hAx : ∀ C ∈ Ax, clSat x C) : clSat x L := by
  induction h with
  | ax hC _ => exact hAx _ hC
  | bool i _ =>
    rcases hx i with h0 | h1
    · exact ⟨(Finsupp.single i 1, 0), by simp, by simp [eSat, lval_single, h0]⟩
    · refine ⟨(Finsupp.single i 1, 1), ?_, ?_⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · simp [eSat, lval_single, h1]
  | weak _ hsub _ ih => obtain ⟨e, he, hv⟩ := ih; exact ⟨e, hsub he, hv⟩
  | comb e1 e2 α β _ _ h1 h2 _ _ ih1 ih2 =>
    obtain ⟨a, ha, hva⟩ := ih1
    obtain ⟨b, hb, hvb⟩ := ih2
    by_cases hae : a = e1
    · by_cases hbe : b = e2
      · subst hae; subst hbe
        refine ⟨_, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
        simp only [eSat] at hva hvb ⊢
        rw [lval_add, lval_smul, lval_smul, hva, hvb]
      · exact ⟨b, Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_erase.2 ⟨hbe, hb⟩)), hvb⟩
    · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_erase.2 ⟨hae, ha⟩)), hva⟩
  | simp _ ih =>
    obtain ⟨e, he, hv⟩ := ih
    rcases Finset.mem_insert.1 he with rfl | he
    · simp [eSat, lval_zero] at hv
    · exact ⟨e, he, hv⟩

end

end RLF

end SATurday.ProofComplexity
