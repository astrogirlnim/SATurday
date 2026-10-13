import Theory.ProofComplexity.ResLinF

/-!
# Normal form and restriction for tree-like Res(lin F) (Ladder Rung R4, Phase 2.2, layer 3a)

Preparation for the size-width relation (Part-Tzameret Theorem 44):

* `RD`: tree-like derivations of unbounded width (sizes are leaf counts).
* `ND`: normal derivations without weakening and without false constant equations `0 = c`
  (`IsZ`); every derivation of a clause yields a normal derivation of a sub-clause with at most as
  many leaves (`rd_to_nd`), and a normal refutation ends in two unit premises (`nd_empty_cases`).
* `elimE`, `rst`: restriction by a hyperplane `ℓ` with pivot variable `i` (the substitution
  `x_i ← (b - ℓ')/c`), acting linearly on equations; restricted derivations are derivations
  (`rd_rst`).

LOG: R4 Phase 2.2 ResLinFNorm module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F]

/-- A false constant equation `0 = c`, `c ≠ 0`. -/
def IsZ (e : LEq F) : Prop := e.1 = 0 ∧ e.2 ≠ 0

/-- Tree-like derivations of unbounded width. -/
inductive RD (Ax : Set (Finset (LEq F))) : Finset (LEq F) → ℕ → Prop
  | ax {C} : C ∈ Ax → RD Ax C 1
  | weak {L L' s} : RD Ax L s → L ⊆ L' → RD Ax L' s
  | comb {A B : Finset (LEq F)} {s1 s2 : ℕ} (e1 e2 : LEq F) (α β : F) :
      RD Ax A s1 → RD Ax B s2 → e1 ∈ A → e2 ∈ B →
      RD Ax (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) (s1 + s2)
  | simp {L s} (c : F) : c ≠ 0 → RD Ax (insert ((0 : ℕ →₀ F), c) L) s → RD Ax L s

theorem rd_of_rld {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s : ℕ}
    (h : RLD Ax w L s) : RD Ax L s := by
  induction h with
  | ax hC _ => exact RD.ax hC
  | weak _ hsub _ ih => exact RD.weak ih hsub
  | comb e1 e2 α β _ _ h1 h2 _ ih1 ih2 => exact RD.comb e1 e2 α β ih1 ih2 h1 h2
  | simp c hc _ ih => exact RD.simp c hc ih

theorem rd_mono_ax {Ax Ax' : Set (Finset (LEq F))} (hA : Ax ⊆ Ax') {L : Finset (LEq F)} {s : ℕ}
    (h : RD Ax L s) : RD Ax' L s := by
  induction h with
  | ax hC => exact RD.ax (hA hC)
  | weak _ hsub ih => exact RD.weak ih hsub
  | comb e1 e2 α β _ _ h1 h2 ih1 ih2 => exact RD.comb e1 e2 α β ih1 ih2 h1 h2
  | simp c hc _ ih => exact RD.simp c hc ih

/-- Normal derivations: leaves are axioms free of false constants, no weakening, resolution
either produces a non false equation or a false constant which is simplified away at once. -/
inductive ND (Ax : Set (Finset (LEq F))) : Finset (LEq F) → ℕ → Prop
  | ax {C} : C ∈ Ax → (∀ e ∈ C, ¬ IsZ e) → ND Ax C 1
  | comb {A B : Finset (LEq F)} {s1 s2 : ℕ} (e1 e2 : LEq F) (α β : F) :
      ND Ax A s1 → ND Ax B s2 → e1 ∈ A → e2 ∈ B → ¬ IsZ (cmb α β e1 e2) →
      ND Ax (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) (s1 + s2)
  | fin {A B : Finset (LEq F)} {s1 s2 : ℕ} (e1 e2 : LEq F) (α β : F) :
      ND Ax A s1 → ND Ax B s2 → e1 ∈ A → e2 ∈ B → IsZ (cmb α β e1 e2) →
      ND Ax (A.erase e1 ∪ B.erase e2) (s1 + s2)

theorem nd_noZ {Ax : Set (Finset (LEq F))} {L : Finset (LEq F)} {s : ℕ} (h : ND Ax L s) :
    ∀ e ∈ L, ¬ IsZ e := by
  induction h with
  | ax _ hC => exact hC
  | comb e1 e2 α β _ _ _ _ hz ih1 ih2 =>
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · rcases Finset.mem_union.1 he with he | he
      · exact ih1 e (Finset.mem_of_mem_erase he)
      · exact ih2 e (Finset.mem_of_mem_erase he)
    · rw [Finset.mem_singleton.1 he]; exact hz
  | fin e1 e2 α β _ _ _ _ _ ih1 ih2 =>
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact ih1 e (Finset.mem_of_mem_erase he)
    · exact ih2 e (Finset.mem_of_mem_erase he)

theorem nd_pos {Ax : Set (Finset (LEq F))} {L : Finset (LEq F)} {s : ℕ} (h : ND Ax L s) :
    1 ≤ s := by
  induction h with
  | ax => exact le_refl _
  | comb _ _ _ _ _ _ _ _ _ ih1 ih2 => omega
  | fin _ _ _ _ _ _ _ _ _ ih1 ih2 => omega

theorem nd_mono_ax {Ax Ax' : Set (Finset (LEq F))} (hA : Ax ⊆ Ax') {L : Finset (LEq F)} {s : ℕ}
    (h : ND Ax L s) : ND Ax' L s := by
  induction h with
  | ax hC hz => exact ND.ax (hA hC) hz
  | comb e1 e2 α β _ _ h1 h2 hz ih1 ih2 => exact ND.comb e1 e2 α β ih1 ih2 h1 h2 hz
  | fin e1 e2 α β _ _ h1 h2 hz ih1 ih2 => exact ND.fin e1 e2 α β ih1 ih2 h1 h2 hz

theorem nd_to_rd {Ax : Set (Finset (LEq F))} {L : Finset (LEq F)} {s : ℕ} (h : ND Ax L s) :
    RD Ax L s := by
  induction h with
  | ax hC _ => exact RD.ax hC
  | comb e1 e2 α β _ _ h1 h2 _ ih1 ih2 => exact RD.comb e1 e2 α β ih1 ih2 h1 h2
  | @fin A B s1 s2 e1 e2 α β _ _ h1 h2 hz ih1 ih2 =>
    refine RD.simp (cmb α β e1 e2).2 hz.2 ?_
    have e := hz.1
    have := RD.comb e1 e2 α β ih1 ih2 h1 h2
    have e' : cmb α β e1 e2 = ((0 : ℕ →₀ F), (cmb α β e1 e2).2) := Prod.ext e rfl
    rw [e'] at this
    rw [Finset.insert_eq, Finset.union_comm]
    exact this

/-- **Normal form**: a derivation of `L` from axioms free of false constants gives a normal
derivation of a sub-clause with at most as many leaves. -/
theorem rd_to_nd {Ax : Set (Finset (LEq F))} (hAx : ∀ C ∈ Ax, ∀ e ∈ C, ¬ IsZ e)
    {L : Finset (LEq F)} {s : ℕ} (h : RD Ax L s) :
    ∃ L0 s0, L0 ⊆ L ∧ s0 ≤ s ∧ ND Ax L0 s0 := by
  induction h with
  | @ax C hC => exact ⟨C, 1, subset_rfl, le_rfl, ND.ax hC (hAx C hC)⟩
  | weak _ hsub ih =>
    obtain ⟨L0, s0, h1, h2, h3⟩ := ih
    exact ⟨L0, s0, h1.trans hsub, h2, h3⟩
  | @comb A B s1 s2 e1 e2 α β _ _ h1 h2 ih1 ih2 =>
    obtain ⟨A0, t1, hA, ht1, nA⟩ := ih1
    obtain ⟨B0, t2, hB, ht2, nB⟩ := ih2
    by_cases m1 : e1 ∈ A0
    · by_cases m2 : e2 ∈ B0
      · by_cases hz : IsZ (cmb α β e1 e2)
        · refine ⟨A0.erase e1 ∪ B0.erase e2, t1 + t2, ?_, by omega, ND.fin e1 e2 α β nA nB m1 m2 hz⟩
          intro x hx
          refine Finset.mem_union_left _ (Finset.mem_union.2 ?_)
          rcases Finset.mem_union.1 hx with hx | hx
          · exact Or.inl (Finset.erase_subset_erase _ hA hx)
          · exact Or.inr (Finset.erase_subset_erase _ hB hx)
        · refine ⟨_, t1 + t2, ?_, by omega, ND.comb e1 e2 α β nA nB m1 m2 hz⟩
          intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · rcases Finset.mem_union.1 hx with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.erase_subset_erase _ hA hx))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.erase_subset_erase _ hB hx))
          · exact Finset.mem_union_right _ hx
      · refine ⟨B0, t2, ?_, by omega, nB⟩
        intro x hx
        refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hB hx⟩))
        rintro rfl; exact m2 hx
    · refine ⟨A0, t1, ?_, by omega, nA⟩
      intro x hx
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hA hx⟩))
      rintro rfl; exact m1 hx
  | @simp L s c hc _ ih =>
    obtain ⟨L0, s0, h1, h2, h3⟩ := ih
    refine ⟨L0, s0, fun x hx => ?_, h2, h3⟩
    rcases Finset.mem_insert.1 (h1 hx) with rfl | h
    · exact absurd ⟨rfl, hc⟩ (nd_noZ h3 _ hx)
    · exact h

/-- A normal refutation is an axiom or ends in a resolution of two units into a false constant. -/
theorem nd_empty_cases {Ax : Set (Finset (LEq F))} {L : Finset (LEq F)} {s : ℕ} (h : ND Ax L s)
    (hL : L = ∅) :
    (∅ ∈ Ax ∧ s = 1) ∨ ∃ (e1 e2 : LEq F) (α β : F) (s1 s2 : ℕ),
      ND Ax {e1} s1 ∧ ND Ax {e2} s2 ∧ IsZ (cmb α β e1 e2) ∧ s = s1 + s2 := by
  cases h with
  | ax hC _ => subst hL; exact Or.inl ⟨hC, rfl⟩
  | comb e1 e2 α β _ _ _ _ _ =>
    exfalso
    have : cmb α β e1 e2 ∈ (∅ : Finset (LEq F)) := by
      rw [← hL]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    simp at this
  | @fin A B s1 s2 e1 e2 α β hA hB h1 h2 hz =>
    right
    have hA1 : A = {e1} := by
      apply Finset.eq_singleton_iff_unique_mem.2 ⟨h1, fun x hx => ?_⟩
      by_contra hne
      have : x ∈ A.erase e1 ∪ B.erase e2 := Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hx⟩)
      rw [hL] at this; simp at this
    have hB1 : B = {e2} := by
      apply Finset.eq_singleton_iff_unique_mem.2 ⟨h2, fun x hx => ?_⟩
      by_contra hne
      have : x ∈ A.erase e1 ∪ B.erase e2 := Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hne, hx⟩)
      rw [hL] at this; simp at this
    subst hA1; subst hB1
    exact ⟨e1, e2, α, β, s1, s2, hA, hB, hz, rfl⟩

end

end RLF

end SATurday.ProofComplexity
