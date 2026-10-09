import Theory.ProofComplexity.ResLin

/-!
# Dag-like resolution over parities (Ladder Rung R4, Phase 2 foundations)

Lines are linear clauses (`LClause`: finite disjunctions of equations `∑_{w∈S} x_w = a` over
`F₂`). A dag-like `Res(⊕)` derivation is a finite set of lines, built one line at a time, each
line justified by lines already present:
* `ax`: an axiom clause of the CNF, read as a linear clause;
* `weak`: a semantic weakening of one earlier line;
* `res`: resolution of weakenings of two earlier lines on a linear form `f`:
  from `C ∨ (f=a)` and `D ∨ (f=a+1)` derive `C ∨ D`.
This is the system of Itsykson–Sokolov with the weakening convention of
Efremenko–Garlik–Itsykson (ECCC TR23-187, section 2.2). Size is the number of distinct lines.
The tree-like system `RLD` of `ResLin.lean` embeds with at most a factor two in size.

LOG: R4 ResLinDag module (dag-like Res(⊕) definitions, soundness, tree embedding)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Finset

/-- Semantic implication between linear clauses. -/
def Imp (L L' : LClause) : Prop := ∀ x, lsatL x L → lsatL x L'

theorem Imp.refl (L : LClause) : Imp L L := fun _ h => h

theorem Imp.trans {L1 L2 L3 : LClause} (h1 : Imp L1 L2) (h2 : Imp L2 L3) : Imp L1 L3 :=
  fun x h => h2 x (h1 x h)

theorem Imp.of_subset {L L' : LClause} (h : L ⊆ L') : Imp L L' :=
  fun _ ⟨e, he, hv⟩ => ⟨e, h he, hv⟩

theorem z2_succ_ne : ∀ a : ZMod 2, a + 1 ≠ a := by decide

/-- One inference step: the line `L` is justified by the set `P` of earlier lines. -/
inductive Step (Ax : Set Clause) (P : Finset LClause) : LClause → Prop
  | ax {C : Clause} : C ∈ Ax → Step Ax P (ofClause C)
  | weak {L0 L : LClause} : L0 ∈ P → Imp L0 L → Step Ax P L
  | res {L1 L2 C D : LClause} {f : Finset ℕ} {a : ZMod 2} :
      L1 ∈ P → L2 ∈ P → Imp L1 (insert (f, a) C) → Imp L2 (insert (f, a + 1) D) →
      Step Ax P (C ∪ D)

/-- Dag-like `Res(⊕)` derivations: finite sets of lines, built from the empty set by adding
one justified line at a time. -/
inductive Der (Ax : Set Clause) : Finset LClause → Prop
  | empty : Der Ax ∅
  | add {P : Finset LClause} {L : LClause} : Der Ax P → Step Ax P L → Der Ax (insert L P)

/-- A dag-like `Res(⊕)` refutation of `Ax` with `s` distinct lines. -/
def DagRefutes (Ax : Set Clause) (s : ℕ) : Prop :=
  ∃ P : Finset LClause, Der Ax P ∧ (∅ : LClause) ∈ P ∧ P.card ≤ s

/-! ## Soundness -/

theorem lsatL_ofClause (x : ℕ → ZMod 2) (C : Clause) :
    lsatL x (ofClause C) ↔ ¬ cfalse x C := by
  unfold lsatL ofClause cfalse
  constructor
  · rintro ⟨e, he, hv⟩ hc
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    exact hc l hl (by simpa [lf] using hv)
  · intro h
    push Not at h
    obtain ⟨l, hl, hs⟩ := h
    exact ⟨_, mem_image.2 ⟨l, hl, rfl⟩, by simpa [lf] using hs⟩

theorem step_sound {Ax : Set Clause} {P : Finset LClause} {L : LClause} (x : ℕ → ZMod 2)
    (hax : ∀ C ∈ Ax, ¬ cfalse x C) (hP : ∀ L' ∈ P, lsatL x L') (h : Step Ax P L) : lsatL x L := by
  induction h with
  | ax hC => exact (lsatL_ofClause x _).2 (hax _ hC)
  | weak h0 hi => exact hi x (hP _ h0)
  | @res L1 L2 C D f a h1 h2 i1 i2 =>
    obtain ⟨e1, he1, hv1⟩ := i1 x (hP _ h1)
    obtain ⟨e2, he2, hv2⟩ := i2 x (hP _ h2)
    by_cases hfa : lf f x = a
    · rcases mem_insert.1 he2 with rfl | he2
      · exfalso; simp only at hv2; rw [hfa] at hv2
        exact z2_succ_ne a hv2.symm
      · exact ⟨e2, mem_union_right _ he2, hv2⟩
    · rcases mem_insert.1 he1 with rfl | he1
      · exact absurd hv1 hfa
      · exact ⟨e1, mem_union_left _ he1, hv1⟩

theorem der_sound {Ax : Set Clause} {P : Finset LClause} (h : Der Ax P) (x : ℕ → ZMod 2)
    (hax : ∀ C ∈ Ax, ¬ cfalse x C) : ∀ L ∈ P, lsatL x L := by
  induction h with
  | empty => simp
  | add _ hs ih =>
    intro L hL
    rcases mem_insert.1 hL with rfl | hL
    · exact step_sound x hax ih hs
    · exact ih L hL

/-- **Soundness**: if the empty clause has a dag-like derivation, every assignment falsifies an
axiom clause. -/
theorem dag_sound {Ax : Set Clause} {s : ℕ} (h : DagRefutes Ax s) (x : ℕ → ZMod 2) :
    ∃ C ∈ Ax, cfalse x C := by
  obtain ⟨P, hD, h0, _⟩ := h
  by_contra hc
  push Not at hc
  obtain ⟨e, he, _⟩ := der_sound hD x (fun C hC hf => hc C hC hf) _ h0
  simp at he

/-! ## Monotonicity and union -/

theorem Step.mono {Ax : Set Clause} {P P' : Finset LClause} {L : LClause} (hP : P ⊆ P')
    (h : Step Ax P L) : Step Ax P' L := by
  cases h with
  | ax hC => exact Step.ax hC
  | weak h0 hi => exact Step.weak (hP h0) hi
  | res h1 h2 i1 i2 => exact Step.res (hP h1) (hP h2) i1 i2

theorem Der.union {Ax : Set Clause} {P1 P2 : Finset LClause} (h1 : Der Ax P1) (h2 : Der Ax P2) :
    Der Ax (P1 ∪ P2) := by
  induction h2 with
  | empty => simpa using h1
  | @add P L _ hs ih =>
    have := Der.add ih (hs.mono (subset_union_right (s₁ := P1)))
    rwa [union_insert]

/-! ## Tree-like derivations are dag-like -/

/-- A tree-like derivation of `L` with `s` axiom leaves gives a dag-like derivation that contains
a line implying `L` and has at most `2 s - 1` lines. -/
theorem rld_to_der {Ax : Set Clause} {L : LClause} {s : ℕ} (h : RLD Ax L s) :
    ∃ P : Finset LClause, Der Ax P ∧ (∃ L0 ∈ P, Imp L0 L) ∧ P.card + 1 ≤ 2 * s := by
  induction h with
  | @ax C hC =>
    refine ⟨{ofClause C}, ?_, ⟨_, mem_singleton_self _, Imp.refl _⟩, by simp⟩
    simpa using Der.add Der.empty (Step.ax hC)
  | weak _ hsub ih =>
    obtain ⟨P, hD, ⟨L0, hL0, hi⟩, hc⟩ := ih
    exact ⟨P, hD, ⟨L0, hL0, hi.trans (Imp.of_subset hsub)⟩, hc⟩
  | @comb C D S1 S2 a1 a2 s1 s2 _ _ ih1 ih2 =>
    obtain ⟨P1, hD1, ⟨L1, hL1, hi1⟩, hc1⟩ := ih1
    obtain ⟨P2, hD2, ⟨L2, hL2, hi2⟩, hc2⟩ := ih2
    -- the second premise is weakened to carry the form `S1 ⊕ S2`
    let D' : LClause := insert (S1, a1 + 1) (D ∪ {(symmDiff S1 S2, a1 + a2)})
    have hi2' : Imp L2 (insert (S1, a1 + 1) (D ∪ {(symmDiff S1 S2, a1 + a2)})) := by
      intro x hx
      obtain ⟨e, he, hv⟩ := hi2 x hx
      rcases mem_insert.1 he with rfl | he
      · simp only at hv
        by_cases h1 : lf S1 x = a1
        · refine ⟨_, mem_insert_of_mem (mem_union_right _ (mem_singleton_self _)), ?_⟩
          simp only [lf_symmDiff, h1, hv]
        · refine ⟨(S1, a1 + 1), mem_insert_self _ _, ?_⟩
          simp only
          rcases z2_cases (lf S1 x) with h | h <;> rcases z2_cases a1 with h' | h' <;>
            simp_all <;> decide
      · exact ⟨e, mem_insert_of_mem (mem_union_left _ he), hv⟩
    have hU := hD1.union hD2
    have hstep : Step Ax (P1 ∪ P2) (C ∪ (D ∪ {(symmDiff S1 S2, a1 + a2)})) :=
      Step.res (f := S1) (a := a1) (mem_union_left _ hL1) (mem_union_right _ hL2) hi1 hi2'
    refine ⟨insert _ (P1 ∪ P2), Der.add hU hstep, ⟨_, mem_insert_self _ _, ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨e, he, hv⟩ := hx
      rw [← union_assoc] at he
      exact ⟨e, by simpa [union_assoc] using he, hv⟩
    · have := card_insert_le (C ∪ (D ∪ {(symmDiff S1 S2, a1 + a2)})) (P1 ∪ P2)
      have := card_union_le P1 P2
      omega
  | simp _ ih =>
    obtain ⟨P, hD, ⟨L0, hL0, hi⟩, hc⟩ := ih
    refine ⟨P, hD, ⟨L0, hL0, hi.trans ?_⟩, hc⟩
    intro x ⟨e, he, hv⟩
    rcases mem_insert.1 he with rfl | he
    · simp [lf] at hv
    · exact ⟨e, he, hv⟩

/-- A tree-like `Res(⊕)` refutation with `s` axiom leaves is a dag-like refutation with at most
`2 s` lines. -/
theorem rld_dagRefutes {Ax : Set Clause} {s : ℕ} (h : RLD Ax ∅ s) : DagRefutes Ax (2 * s) := by
  obtain ⟨P, hD, ⟨L0, hL0, hi⟩, hc⟩ := rld_to_der h
  have hstep : Step Ax P ∅ := Step.weak hL0 (fun x hx => by
    obtain ⟨e, he, hv⟩ := hi x hx; simp at he)
  refine ⟨insert ∅ P, Der.add hD hstep, mem_insert_self _ _, ?_⟩
  have := card_insert_le (∅ : LClause) P
  omega

end

end RL

end SATurday.ProofComplexity
