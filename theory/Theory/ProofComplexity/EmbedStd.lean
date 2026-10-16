import Theory.ProofComplexity.ResLinFDag
import Theory.ProofComplexity.ResLinDag

/-!
# Standard `Res(lin F)` and `Res(⊕)` as sequences of lines, and size-controlled embeddings

This file turns the informal comparisons "our dag system is the standard one" into theorems.
It defines the two textbook systems literally, as *sequences* of lines (lists) in which every
line is justified by earlier lines, with the number of lines as the size, and proves embeddings
in both directions with explicit size bounds.

## Standard `Res(lin F)` (`RLF.StdLin`)

Source: Part and Tzameret, "Resolution with counting: dag-like lower bounds and different
moduli" (arXiv 1806.09383v2, Section 1.1.1, after Raz and Tzameret). A refutation is a sequence
of linear clauses; each is an input clause, a Boolean axiom `x_i = 0 ∨ x_i = 1`, or derived by
* resolution: from `C ∨ f` and `D ∨ g` derive `C ∨ D ∨ (αf + βg)` (`α, β ∈ F` arbitrary),
* weakening: extend a clause with arbitrary disjuncts,
* simplification: discard a false constant equation `0 = c`, `c ≠ 0`.
Clauses are sets (duplicates contracted). **Size caveat:** Part and Tzameret measure the total
symbol size (variable occurrences plus coefficient sizes); here the size is the number of lines.
Every line has symbol size `≥ 1`, so a lower bound on the number of lines is a lower bound on
their symbol size, but not conversely: an upper bound on lines does not bound symbol size.

Results: `stdLin_to_rldag` (every standard derivation of `ℓ` lines gives an `RLDag`
derivation with at most `2ℓ` lines) and `rldag_to_stdLin` (every `RLDag` derivation with `n`
lines gives a standard derivation of exactly `n` lines). So `RLDag` is the standard system, and
the factor 2 only comes from the resolution rule of Part and Tzameret allowing extra disjuncts
in the conclusion, which `RLDag` expresses by a following weakening.

## Standard `Res(⊕)` (`RL.StdXor`)

Source: Itsykson and Sokolov (Res(⊕), APAL 2020) in the formulation of, e.g.,
Bhattacharya, Chattopadhyay and Dvorak, "Exponential separation between powers of regular and
general resolution over parities" (arXiv 2402.04364, Section 3): resolution `A ∨ (ℓ = 0)`,
`B ∨ (ℓ = 1) ⊢ A ∨ B`, and weakening. The size is the number of rule applications. Two
conventions occur: weakening to a semantically implied clause (BCD, EGI: `StdXor true`) and
weakening to a superset (`StdXor false`). `RL.DagRefutes` is the semantic one with the
weakening of the two resolution premises fused into the resolution step.

Results: `stdXor_to_dag` (either convention; `ℓ` lines give at most `ℓ` lines of `Der`),
`dag_to_stdXor` (`n` lines of `Der` give a semantic standard derivation of at most `3n` lines).
-/

namespace SATurday.ProofComplexity

open scoped Classical

noncomputable section

namespace RLF

variable {F : Type} [Field F]

/-- One step of standard `Res(lin F)` (Part-Tzameret), from the earlier lines `P`. -/
inductive StdStep (Ax : Set (Finset (LEq F))) (P : List (Finset (LEq F))) :
    Finset (LEq F) → Prop
  | ax {C} : C ∈ Ax → StdStep Ax P C
  | bool (i : ℕ) : StdStep Ax P (boolCl i)
  | weak {L} (L' : Finset (LEq F)) : L ∈ P → L ⊆ L' → StdStep Ax P L'
  | res {C D : Finset (LEq F)} (e1 e2 : LEq F) (α β : F) :
      insert e1 C ∈ P → insert e2 D ∈ P → StdStep Ax P (C ∪ D ∪ {cmb α β e1 e2})
  | simp {L : Finset (LEq F)} (c : F) : c ≠ 0 → insert ((0 : ℕ →₀ F), c) L ∈ P → StdStep Ax P L

/-- Standard `Res(lin F)` derivations: lists of lines, each justified by the earlier ones. -/
inductive StdDer (Ax : Set (Finset (LEq F))) : List (Finset (LEq F)) → Prop
  | nil : StdDer Ax []
  | snoc {l L} : StdDer Ax l → StdStep Ax l L → StdDer Ax (l ++ [L])

/-- A standard refutation with at most `s` lines: a derivation containing the empty clause. -/
def StdLinRefutes (Ax : Set (Finset (LEq F))) (s : ℕ) : Prop :=
  ∃ l, StdDer Ax l ∧ (∅ : Finset (LEq F)) ∈ l ∧ l.length ≤ s

theorem stdLin_to_rldag {Ax : Set (Finset (LEq F))} {l : List (Finset (LEq F))}
    (h : StdDer Ax l) :
    ∃ 𝓛, RLDag (Ax ∪ boolAx) 𝓛 ∧ (∀ L ∈ l, L ∈ 𝓛) ∧ 𝓛.card ≤ 2 * l.length := by
  induction h with
  | nil => exact ⟨∅, RLDag.empty, by simp, by simp⟩
  | @snoc l L _ hs ih =>
    obtain ⟨𝓛, hD, hmem, hc⟩ := ih
    have key : ∃ 𝓛', RLDag (Ax ∪ boolAx) 𝓛' ∧ L ∈ 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 := by
      cases hs with
      | ax hC =>
        refine ⟨insert L 𝓛, RLDag.ax L hD (Or.inl hC), Finset.mem_insert_self _ _,
          Finset.subset_insert _ _, ?_⟩
        have := Finset.card_insert_le L 𝓛; omega
      | bool i =>
        refine ⟨insert (boolCl i) 𝓛, RLDag.ax _ hD (Or.inr (boolCl_mem_boolAx i)),
          Finset.mem_insert_self _ _, Finset.subset_insert _ _, ?_⟩
        have := Finset.card_insert_le (boolCl i) 𝓛; omega
      | @weak L0 _ hL hsub =>
        refine ⟨insert L 𝓛, RLDag.weak _ L hD (hmem _ hL) hsub, Finset.mem_insert_self _ _,
          Finset.subset_insert _ _, ?_⟩
        have := Finset.card_insert_le L 𝓛; omega
      | @res C D e1 e2 α β h1 h2 =>
        have hA := hmem _ h1
        have hB := hmem _ h2
        have hc1 := RLDag.comb (insert e1 C) (insert e2 D) e1 e2 α β hD hA hB
          (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
        have hsub : (insert e1 C).erase e1 ∪ (insert e2 D).erase e2 ∪ {cmb α β e1 e2} ⊆
            C ∪ D ∪ {cmb α β e1 e2} := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton] at hx ⊢
          tauto
        refine ⟨insert (C ∪ D ∪ {cmb α β e1 e2}) (insert ((insert e1 C).erase e1 ∪
            (insert e2 D).erase e2 ∪ {cmb α β e1 e2}) 𝓛),
          RLDag.weak _ _ hc1 (Finset.mem_insert_self _ _) hsub, Finset.mem_insert_self _ _,
          fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx), ?_⟩
        have := Finset.card_insert_le (C ∪ D ∪ {cmb α β e1 e2}) (insert ((insert e1 C).erase e1 ∪
            (insert e2 D).erase e2 ∪ {cmb α β e1 e2}) 𝓛)
        have := Finset.card_insert_le ((insert e1 C).erase e1 ∪
            (insert e2 D).erase e2 ∪ {cmb α β e1 e2}) 𝓛
        omega
      | simp c hc h0 =>
        refine ⟨insert L 𝓛, RLDag.simp L c hD hc (hmem _ h0), Finset.mem_insert_self _ _,
          Finset.subset_insert _ _, ?_⟩
        have := Finset.card_insert_le L 𝓛; omega
    obtain ⟨𝓛', hD', hL, hsub, hc'⟩ := key
    refine ⟨𝓛', hD', ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsub (hmem x hx)
      · rw [List.mem_singleton.1 hx]; exact hL
    · simp only [List.length_append, List.length_singleton]; omega

/-- Every standard `Res(lin F)` refutation of `s` lines gives an `RLDag` refutation
(a set of lines containing the empty clause) with at most `2 s` lines. -/
theorem stdLin_refutes_to_rldag {Ax : Set (Finset (LEq F))} {s : ℕ}
    (h : StdLinRefutes Ax s) :
    ∃ 𝓛, RLDag (Ax ∪ boolAx) 𝓛 ∧ (∅ : Finset (LEq F)) ∈ 𝓛 ∧ 𝓛.card ≤ 2 * s := by
  obtain ⟨l, hD, h0, hl⟩ := h
  obtain ⟨𝓛, hD', hmem, hc⟩ := stdLin_to_rldag hD
  exact ⟨𝓛, hD', hmem _ h0, by omega⟩

theorem rldag_to_stdLin {Ax : Set (Finset (LEq F))} {𝓛 : Finset (Finset (LEq F))}
    (h : RLDag (Ax ∪ boolAx) 𝓛) :
    ∃ l, StdDer Ax l ∧ l.Nodup ∧ l.toFinset = 𝓛 := by
  induction h with
  | empty => exact ⟨[], StdDer.nil, List.nodup_nil, by simp⟩
  | @ax 𝓛 C _ hC ih =>
    obtain ⟨l, hD, hnd, hl⟩ := ih
    by_cases hm : C ∈ 𝓛
    · exact ⟨l, hD, hnd, by rw [hl, Finset.insert_eq_of_mem hm]⟩
    · have hC' : C ∈ Ax ∨ C ∈ boolAx := hC
      have hstep : StdStep Ax l C := by
        rcases hC' with hC' | ⟨i, rfl⟩
        · exact StdStep.ax hC'
        · exact StdStep.bool i
      refine ⟨l ++ [C], StdDer.snoc hD hstep, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy
        apply hm; rw [← hl]; exact List.mem_toFinset.2 hx
      · ext x; simp [hl]
  | @weak 𝓛 L L' _ hL hsub ih =>
    obtain ⟨l, hD, hnd, hl⟩ := ih
    by_cases hm : L' ∈ 𝓛
    · exact ⟨l, hD, hnd, by rw [hl, Finset.insert_eq_of_mem hm]⟩
    · have hLl : L ∈ l := by rw [← List.mem_toFinset, hl]; exact hL
      refine ⟨l ++ [L'], StdDer.snoc hD (StdStep.weak L' hLl hsub), ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy
        apply hm; rw [← hl]; exact List.mem_toFinset.2 hx
      · ext x; simp [hl]
  | @comb 𝓛 A B e1 e2 α β _ hA hB h1 h2 ih =>
    obtain ⟨l, hD, hnd, hl⟩ := ih
    set T := A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2} with hT
    by_cases hm : T ∈ 𝓛
    · exact ⟨l, hD, hnd, by rw [hl, Finset.insert_eq_of_mem hm]⟩
    · have hAl : insert e1 (A.erase e1) ∈ l := by
        rw [Finset.insert_erase h1, ← List.mem_toFinset, hl]; exact hA
      have hBl : insert e2 (B.erase e2) ∈ l := by
        rw [Finset.insert_erase h2, ← List.mem_toFinset, hl]; exact hB
      refine ⟨l ++ [T], StdDer.snoc hD (StdStep.res (C := A.erase e1) (D := B.erase e2)
        e1 e2 α β hAl hBl), ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy
        apply hm; rw [← hl]; exact List.mem_toFinset.2 hx
      · ext x; simp [hl]
  | @simp 𝓛 L c _ hc h0 ih =>
    obtain ⟨l, hD, hnd, hl⟩ := ih
    by_cases hm : L ∈ 𝓛
    · exact ⟨l, hD, hnd, by rw [hl, Finset.insert_eq_of_mem hm]⟩
    · have h0l : insert ((0 : ℕ →₀ F), c) L ∈ l := by rw [← List.mem_toFinset, hl]; exact h0
      refine ⟨l ++ [L], StdDer.snoc hD (StdStep.simp c hc h0l), ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy
        apply hm; rw [← hl]; exact List.mem_toFinset.2 hx
      · ext x; simp [hl]

/-- Every `RLDag` refutation with `n` lines is a standard `Res(lin F)` refutation with
exactly `n` lines (no loss). -/
theorem rldag_refutes_to_stdLin {Ax : Set (Finset (LEq F))} {𝓛 : Finset (Finset (LEq F))}
    (h : RLDag (Ax ∪ boolAx) 𝓛) (h0 : (∅ : Finset (LEq F)) ∈ 𝓛) :
    StdLinRefutes Ax 𝓛.card := by
  obtain ⟨l, hD, hnd, hl⟩ := rldag_to_stdLin h
  refine ⟨l, hD, ?_, ?_⟩
  · rw [← List.mem_toFinset, hl]; exact h0
  · rw [← hl, List.toFinset_card_of_nodup hnd]

end RLF

/-! ## Standard `Res(⊕)` -/

namespace RL

/-- Weakening convention: `true` semantic (`Imp`), `false` superset. -/
def WOK (sem : Bool) (L0 L : LClause) : Prop := if sem then Imp L0 L else L0 ⊆ L

theorem WOK.imp {sem : Bool} {L0 L : LClause} (h : WOK sem L0 L) : Imp L0 L := by
  cases sem
  · exact Imp.of_subset h
  · exact h

/-- One step of standard `Res(⊕)` (Itsykson-Sokolov; resolution and weakening) from the earlier
lines `P`. -/
inductive XStep (sem : Bool) (Ax : Set Clause) (P : List LClause) : LClause → Prop
  | ax {C : Clause} : C ∈ Ax → XStep sem Ax P (ofClause C)
  | weak {L0 L : LClause} : L0 ∈ P → WOK sem L0 L → XStep sem Ax P L
  | res {A B : LClause} (f : Finset ℕ) (a : ZMod 2) :
      insert (f, a) A ∈ P → insert (f, a + 1) B ∈ P → XStep sem Ax P (A ∪ B)

/-- Standard `Res(⊕)` derivations as lists of lines. -/
inductive XDer (sem : Bool) (Ax : Set Clause) : List LClause → Prop
  | nil : XDer sem Ax []
  | snoc {l L} : XDer sem Ax l → XStep sem Ax l L → XDer sem Ax (l ++ [L])

/-- A standard `Res(⊕)` refutation with at most `s` lines. -/
def StdXorRefutes (sem : Bool) (Ax : Set Clause) (s : ℕ) : Prop :=
  ∃ l, XDer sem Ax l ∧ (∅ : LClause) ∈ l ∧ l.length ≤ s

theorem stdXor_to_der {sem : Bool} {Ax : Set Clause} {l : List LClause} (h : XDer sem Ax l) :
    ∃ P, Der Ax P ∧ (∀ L ∈ l, L ∈ P) ∧ P.card ≤ l.length := by
  induction h with
  | nil => exact ⟨∅, Der.empty, by simp, by simp⟩
  | @snoc l L _ hs ih =>
    obtain ⟨P, hD, hmem, hc⟩ := ih
    have hst : Step Ax P L := by
      cases hs with
      | ax hC => exact Step.ax hC
      | weak h0 hw => exact Step.weak (hmem _ h0) hw.imp
      | res f a h1 h2 =>
        exact Step.res (hmem _ h1) (hmem _ h2) (Imp.refl _) (Imp.refl _)
    refine ⟨insert L P, Der.add hD hst, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Finset.mem_insert_of_mem (hmem x hx)
      · rw [List.mem_singleton.1 hx]; exact Finset.mem_insert_self _ _
    · have := Finset.card_insert_le L P
      simp only [List.length_append, List.length_singleton]; omega

/-- A standard `Res(⊕)` refutation (either weakening convention) of `s` lines is a dag-like
refutation `RL.DagRefutes` with at most `s` lines: the embedding of the standard syntactic system
into ours loses nothing. -/
theorem stdXor_refutes_to_dag {sem : Bool} {Ax : Set Clause} {s : ℕ}
    (h : StdXorRefutes sem Ax s) : DagRefutes Ax s := by
  obtain ⟨l, hD, h0, hl⟩ := h
  obtain ⟨P, hD', hmem, hc⟩ := stdXor_to_der hD
  exact ⟨P, hD', hmem _ h0, by omega⟩

theorem der_to_stdXor {Ax : Set Clause} {P : Finset LClause} (h : Der Ax P) :
    ∃ l, XDer true Ax l ∧ (∀ L ∈ P, L ∈ l) ∧ l.length ≤ 3 * P.card := by
  induction h with
  | empty => exact ⟨[], XDer.nil, by simp, by simp⟩
  | @add P L hD hs ih =>
    obtain ⟨l, hl, hmem, hc⟩ := ih
    by_cases hLP : L ∈ P
    · refine ⟨l, hl, ?_, by rw [Finset.insert_eq_of_mem hLP]; exact hc⟩
      intro x hx
      exact hmem x (by rw [Finset.insert_eq_of_mem hLP] at hx; exact hx)
    · have hcard : (insert L P).card = P.card + 1 := Finset.card_insert_of_notMem hLP
      cases hs with
      | ax hC =>
        refine ⟨l ++ [ofClause _], XDer.snoc hl (XStep.ax hC), ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp
          · exact List.mem_append_left _ (hmem x hx)
        · simp only [List.length_append, List.length_singleton]; omega
      | @weak L0 _ h0 hi =>
        refine ⟨l ++ [L], XDer.snoc hl (XStep.weak (hmem _ h0) (by simpa [WOK] using hi)), ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp
          · exact List.mem_append_left _ (hmem x hx)
        · simp only [List.length_append, List.length_singleton]; omega
      | @res L1 L2 C D f a h1 h2 i1 i2 =>
        have s1 : XStep true Ax l (insert (f, a) C) := XStep.weak (hmem _ h1) (by simpa [WOK] using i1)
        have d1 := XDer.snoc hl s1
        have s2 : XStep true Ax (l ++ [insert (f, a) C]) (insert (f, a + 1) D) :=
          XStep.weak (List.mem_append_left _ (hmem _ h2)) (by simpa [WOK] using i2)
        have d2 := XDer.snoc d1 s2
        have s3 : XStep true Ax (l ++ [insert (f, a) C] ++ [insert (f, a + 1) D]) (C ∪ D) :=
          XStep.res f a (by simp) (by simp)
        refine ⟨l ++ [insert (f, a) C] ++ [insert (f, a + 1) D] ++ [C ∪ D],
          XDer.snoc d2 s3, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp
          · simp [hmem x hx]
        · simp only [List.length_append, List.length_singleton]; omega

/-- Conversely, every dag-like refutation `RL.DagRefutes` with `s` lines is a standard `Res(⊕)`
refutation with semantic weakening (the convention of Bhattacharya-Chattopadhyay-Dvorak and
Efremenko-Garlik-Itsykson) with at most `3 s` lines: each of our resolution steps fuses two
weakenings and one resolution. -/
theorem dag_to_stdXor_refutes {Ax : Set Clause} {s : ℕ} (h : DagRefutes Ax s) :
    StdXorRefutes true Ax (3 * s) := by
  obtain ⟨P, hD, h0, hc⟩ := h
  obtain ⟨l, hl, hmem, hlen⟩ := der_to_stdXor hD
  exact ⟨l, hl, hmem _ h0, by omega⟩

end RL

end

end SATurday.ProofComplexity
