import Theory.ProofComplexity.ResLinF

/-!
# Dag-like Res(lin F) (Ladder Rung R4, Phase 2.2, Khaniki layer K1)

`RLDag Ax 𝓛`: the finite set `𝓛` of linear clauses is built from the empty set by adding lines
that are axioms, weakenings of a line, resolution combinations of two lines (`C ∨ f = a`,
`D ∨ g = b` ⊢ `C ∨ D ∨ αf+βg = αa+βb`) or simplifications of a false constant equation. No width
bound; the dag-like size is `𝓛.card` (the number of distinct lines). A refutation is such a set
containing the empty clause. Soundness is `rldag_sound`.

LOG: R4 Phase 2.2 ResLinFDag module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F]

/-- Dag-like `Res(lin F)` from the clause set `Ax` (which is to contain `boolAx`). -/
inductive RLDag (Ax : Set (Finset (LEq F))) : Finset (Finset (LEq F)) → Prop
  | empty : RLDag Ax ∅
  | ax {𝓛} (C : Finset (LEq F)) : RLDag Ax 𝓛 → C ∈ Ax → RLDag Ax (insert C 𝓛)
  | weak {𝓛} (L L' : Finset (LEq F)) : RLDag Ax 𝓛 → L ∈ 𝓛 → L ⊆ L' → RLDag Ax (insert L' 𝓛)
  | comb {𝓛} (A B : Finset (LEq F)) (e1 e2 : LEq F) (α β : F) :
      RLDag Ax 𝓛 → A ∈ 𝓛 → B ∈ 𝓛 → e1 ∈ A → e2 ∈ B →
      RLDag Ax (insert (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) 𝓛)
  | simp {𝓛} (L : Finset (LEq F)) (c : F) : RLDag Ax 𝓛 → c ≠ 0 →
      insert ((0 : ℕ →₀ F), c) L ∈ 𝓛 → RLDag Ax (insert L 𝓛)

/-- **Soundness**: every line of a dag derivation holds at a Boolean point satisfying the axioms. -/
theorem rldag_sound {Ax : Set (Finset (LEq F))} {𝓛 : Finset (Finset (LEq F))} (h : RLDag Ax 𝓛)
    {x : ℕ → F} (hAx : ∀ C ∈ Ax, clSat x C) : ∀ L ∈ 𝓛, clSat x L := by
  induction h with
  | empty => intro L hL; simp at hL
  | ax C _ hC ih =>
    intro L hL
    rcases Finset.mem_insert.1 hL with rfl | hL
    · exact hAx _ hC
    · exact ih L hL
  | weak L0 L' _ hL0 hsub ih =>
    intro L hL
    rcases Finset.mem_insert.1 hL with rfl | hL
    · obtain ⟨e, he, hv⟩ := ih L0 hL0
      exact ⟨e, hsub he, hv⟩
    · exact ih L hL
  | comb A B e1 e2 α β _ hA hB h1 h2 ih =>
    intro L hL
    rcases Finset.mem_insert.1 hL with rfl | hL
    · obtain ⟨a, ha, hva⟩ := ih A hA
      obtain ⟨b, hb, hvb⟩ := ih B hB
      by_cases hae : a = e1
      · by_cases hbe : b = e2
        · subst hae; subst hbe
          refine ⟨_, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
          simp only [eSat, cmb] at hva hvb ⊢
          rw [lval_add, lval_smul, lval_smul, hva, hvb]
        · exact ⟨b, Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_erase.2 ⟨hbe, hb⟩)), hvb⟩
      · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.2 ⟨hae, ha⟩)), hva⟩
    · exact ih L hL
  | simp L0 c _ hc hL0 ih =>
    intro L hL
    rcases Finset.mem_insert.1 hL with rfl | hL
    · obtain ⟨e, he, hv⟩ := ih _ hL0
      rcases Finset.mem_insert.1 he with rfl | he
      · simp [eSat, lval_zero] at hv; exact absurd hv.symm hc
      · exact ⟨e, he, hv⟩
    · exact ih L hL

end

end RLF

end SATurday.ProofComplexity
