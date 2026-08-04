import Theory.ProofComplexity.MatchingRestriction

/-!
# Resolution Width Measures and Restriction Transport (Ladder Rung R2)

First formalize chunk of the Ben-Sasson and Wigderson size versus width
tradeoff pinned in docs/ladder/rungs/r2-width-machinery.md:

1. Width and fat-count measures on `Derivation` trees.
2. Single-variable assignments `assignOne` feeding the existing
   `restrictClause` / `restrictCNF` API.
3. Width and fat-count preserving restriction surgery
   (`exists_derivation_restrict_width`), strengthening the size-only
   `derivation_restrict_sub` from MatchingRestriction.lean.

`fatShrink`, `fatSteps`, the core tradeoff, and the rate corollary live in
SizeWidth.lean (next formalize cycles). Certified R0 and R1 modules are not
edited here.

LOG: R2 width measures and restrict-width transport
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Width of a CNF and literal universe -/

/-- Initial width: largest clause cardinality in the hypothesis CNF. -/
noncomputable def cnfWidth (F : CNF) : ℕ := F.sup Finset.card

/-- Both polarities of every variable of `F`. Cardinality is twice
`(cnfVars F).card`. -/
noncomputable def cnfLits (F : CNF) : Finset Literal :=
  (cnfVars F).biUnion fun v => {⟨v, true⟩, ⟨v, false⟩}

private theorem litPair_card (v : ℕ) :
    ({⟨v, true⟩, ⟨v, false⟩} : Finset Literal).card = 2 := by
  simp

private theorem litPair_disjoint {x y : ℕ} (hne : x ≠ y) :
    Disjoint ({⟨x, true⟩, ⟨x, false⟩} : Finset Literal)
      ({⟨y, true⟩, ⟨y, false⟩} : Finset Literal) := by
  refine disjoint_left.mpr ?_
  intro z hzx hzy
  simp only [mem_insert, mem_singleton] at hzx hzy
  rcases hzx with rfl | rfl <;> rcases hzy with hy | hy
  · exact hne (congrArg Literal.var hy)
  · exact Bool.noConfusion (congrArg Literal.pos hy)
  · exact Bool.noConfusion (congrArg Literal.pos hy).symm
  · exact hne (congrArg Literal.var hy)

theorem cnfLits_card (F : CNF) : (cnfLits F).card = 2 * (cnfVars F).card := by
  simp only [cnfLits]
  rw [card_biUnion (fun x _ y _ hne => litPair_disjoint hne)]
  rw [Finset.sum_congr rfl fun v _ => litPair_card v]
  simp [sum_const, smul_eq_mul, mul_comm]

/-! ## Single-variable partial assignment -/

/-- Force variable `x` to boolean value `b`; leave every other variable unset. -/
def assignOne (x : ℕ) (b : Bool) : ℕ → Option Bool :=
  fun v => if v = x then some b else none

theorem assignOne_self (x : ℕ) (b : Bool) : assignOne x b x = some b := by
  simp [assignOne]

theorem assignOne_ne {x v : ℕ} (b : Bool) (h : v ≠ x) : assignOne x b v = none := by
  simp [assignOne, h]

/-! ## Derivation lines, width, and fat counts -/

/-- All conclusion clauses appearing in a derivation tree (as a Finset). -/
noncomputable def Derivation.lines {F : CNF} : {C : Clause} → Derivation F C → Finset Clause
  | _, .hyp C _ => {C}
  | _, .res x dC dD _ _ =>
      insert (resolvent dC.conclusion dD.conclusion x) (dC.lines ∪ dD.lines)

theorem Derivation.concl_mem_lines {F : CNF} {C : Clause} (d : Derivation F C) :
    C ∈ d.lines := by
  cases d with
  | hyp _ _ => simp [Derivation.lines]
  | res _ _ _ _ _ => simp [Derivation.lines, Derivation.conclusion]

/-- Tree size dominates the number of distinct lines. -/
theorem Derivation.lines_card_le_size {F : CNF} {C : Clause} (d : Derivation F C) :
    d.lines.card ≤ d.size := by
  induction d with
  | hyp _ _ => simp [Derivation.lines, Derivation.size]
  | res x dC dD _ _ ihC ihD =>
      simp only [Derivation.lines, Derivation.size]
      have h1 :=
        card_insert_le (resolvent dC.conclusion dD.conclusion x) (dC.lines ∪ dD.lines)
      have h2 := card_union_le dC.lines dD.lines
      omega

/-- Maximum clause cardinality over the derivation tree. -/
def Derivation.width {F : CNF} : {C : Clause} → Derivation F C → ℕ
  | _, .hyp C _ => C.card
  | _, .res x dC dD _ _ =>
      max (max dC.width dD.width) (resolvent dC.conclusion dD.conclusion x).card

/-- Number of tree nodes whose clause has cardinality strictly above `t`. -/
def Derivation.fatCount (t : ℕ) {F : CNF} : {C : Clause} → Derivation F C → ℕ
  | _, .hyp C _ => if C.card > t then 1 else 0
  | _, .res x dC dD _ _ =>
      dC.fatCount t + dD.fatCount t +
        if (resolvent dC.conclusion dD.conclusion x).card > t then 1 else 0

/-- Number of fat nodes containing a given literal. -/
def Derivation.fatLitCount (t : ℕ) (l : Literal) {F : CNF} :
    {C : Clause} → Derivation F C → ℕ
  | _, .hyp C _ => if C.card > t ∧ l ∈ C then 1 else 0
  | _, .res x dC dD _ _ =>
      dC.fatLitCount t l + dD.fatLitCount t l +
        if (resolvent dC.conclusion dD.conclusion x).card > t ∧
            l ∈ resolvent dC.conclusion dD.conclusion x then
          1
        else
          0

theorem Derivation.fatCount_le_size (t : ℕ) {F : CNF} {C : Clause}
    (d : Derivation F C) : d.fatCount t ≤ d.size := by
  induction d with
  | hyp C _ =>
      simp only [Derivation.fatCount, Derivation.size]
      split_ifs <;> omega
  | res x dC dD _ _ ihC ihD =>
      simp only [Derivation.fatCount, Derivation.size]
      split_ifs <;> omega

/-- Hypothesis clauses cannot exceed the CNF width. -/
theorem Derivation.width_hyp_le_cnfWidth {F : CNF} {C : Clause}
    (hC : C ∈ F) : C.card ≤ cnfWidth F :=
  le_sup hC

/-- If no node is fat above `t`, width is at most `max (cnfWidth F) t`. -/
theorem width_le_of_fatCount_zero {F : CNF} {C : Clause} (d : Derivation F C) (t : ℕ)
    (h : d.fatCount t = 0) : d.width ≤ max (cnfWidth F) t := by
  induction d with
  | hyp C hC =>
      simp only [Derivation.fatCount, Derivation.width] at h ⊢
      by_cases hfat : C.card > t
      · simp [hfat] at h
      · exact (Derivation.width_hyp_le_cnfWidth hC).trans (le_max_left _ _)
  | res x dC dD _ _ ihC ihD =>
      simp only [Derivation.fatCount, Derivation.width] at h ⊢
      by_cases hfat : (resolvent dC.conclusion dD.conclusion x).card > t
      · simp [hfat] at h
      · simp only [hfat, ↓reduceIte] at h
        have hC0 : dC.fatCount t = 0 := by omega
        have hD0 : dD.fatCount t = 0 := by omega
        have hRle : (resolvent dC.conclusion dD.conclusion x).card ≤ t :=
          Nat.le_of_not_gt hfat
        exact max_le (max_le (ihC hC0) (ihD hD0)) (le_max_of_le_right hRle)

/-! ## Restriction shrinks width and variables -/

theorem cnfWidth_restrictCNF_le (ρ : ℕ → Option Bool) (F : CNF) :
    cnfWidth (restrictCNF ρ F) ≤ cnfWidth F := by
  refine Finset.sup_le ?_
  intro C' hC'
  obtain ⟨C, hC, hres⟩ := (mem_restrictCNF_iff ρ F C').mp hC'
  exact (card_le_card (restrictClause_subset hres)).trans
    (Derivation.width_hyp_le_cnfWidth hC)

/-- Assigned variables never appear in a restricted CNF. -/
theorem notMem_cnfVars_restrictCNF_of_assigned {ρ : ℕ → Option Bool} {F : CNF}
    {x : ℕ} (hx : ρ x ≠ none) : x ∉ cnfVars (restrictCNF ρ F) := by
  intro hxmem
  obtain ⟨C', hC', l, hl, rfl⟩ := mem_cnfVars.mp hxmem
  obtain ⟨C, hC, hres⟩ := (mem_restrictCNF_iff ρ F C').mp hC'
  have ⟨_, hC'eq⟩ := (restrictClause_eq_some_iff ρ C C').mp hres
  have hl' : l ∈ C.filter fun lit => ρ lit.var = none := by
    simpa [hC'eq] using hl
  have hun : ρ l.var = none := (mem_filter.mp hl').2
  exact hx hun

theorem cnfVars_restrictCNF_subset (ρ : ℕ → Option Bool) (F : CNF) :
    cnfVars (restrictCNF ρ F) ⊆ cnfVars F := by
  intro v hv
  obtain ⟨C', hC', l, hl, rfl⟩ := mem_cnfVars.mp hv
  obtain ⟨C, hC, hres⟩ := (mem_restrictCNF_iff ρ F C').mp hC'
  exact mem_cnfVars.mpr ⟨C, hC, l, restrictClause_subset hres hl, rfl⟩

theorem cnfVars_restrictCNF_ssubset_assignOne {F : CNF} {x : ℕ} (b : Bool)
    (hx : x ∈ cnfVars F) :
    cnfVars (restrictCNF (assignOne x b) F) ⊂ cnfVars F := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨cnfVars_restrictCNF_subset _ F, ?_⟩
  intro heq
  have : x ∈ cnfVars (restrictCNF (assignOne x b) F) := by
    rw [heq]; exact hx
  exact notMem_cnfVars_restrictCNF_of_assigned (by simp [assignOne]) this

/-! ## Width and fat-count preserving restriction surgery -/

theorem card_le_of_subset {C D : Clause} (h : C ⊆ D) : C.card ≤ D.card :=
  card_le_card h

/-- Resolvent of subclauses is a subclause of the resolvent. -/
theorem resolvent_subset_of_subset {C C' D D' : Clause} {x : ℕ}
    (hC : C' ⊆ C) (hD : D' ⊆ D) :
    resolvent C' D' x ⊆ resolvent C D x := by
  intro l hl
  have hl' : l ∈ C'.erase ⟨x, true⟩ ∨ l ∈ D'.erase ⟨x, false⟩ :=
    (mem_union).mp (by simpa [resolvent] using hl)
  simp only [resolvent, mem_union, mem_erase]
  rcases hl' with hlC | hlD
  · obtain ⟨hlne, hlC⟩ := mem_erase.mp hlC
    exact Or.inl ⟨hlne, hC hlC⟩
  · obtain ⟨hlne, hlD⟩ := mem_erase.mp hlD
    exact Or.inr ⟨hlne, hD hlD⟩

/-- Strengthening of `derivation_restrict_sub`: the restricted derivation also
obeys width and fat-count bounds relative to the original tree. -/
theorem exists_derivation_restrict_width (ρ : ℕ → Option Bool) {F : CNF}
    {C : Clause} (d : Derivation F C) {C' : Clause}
    (hC' : restrictClause ρ C = some C') :
    ∃ D : Clause, ∃ d' : Derivation (restrictCNF ρ F) D,
      D ⊆ C' ∧ d'.size ≤ d.size ∧ d'.width ≤ d.width ∧
        ∀ t, d'.fatCount t ≤ d.fatCount t := by
  induction d generalizing C' with
  | hyp C hC =>
      refine ⟨C', Derivation.hyp C' ?mem, Subset.rfl, ?sz, ?wd, ?fat⟩
      case mem => exact (mem_restrictCNF_iff ρ F C').mpr ⟨C, hC, hC'⟩
      case sz => simp [Derivation.size]
      case wd =>
        simp only [Derivation.width]
        exact card_le_of_subset (restrictClause_subset hC')
      case fat =>
        intro t
        simp only [Derivation.fatCount]
        by_cases hfatC' : C'.card > t
        · simp only [hfatC', ↓reduceIte]
          have hle := card_le_of_subset (restrictClause_subset hC')
          have hfatC : C.card > t := Nat.lt_of_lt_of_le hfatC' hle
          simp [hfatC]
        · simp [hfatC']
  | res x dC dD hx hnx ihC ihD =>
      change restrictClause ρ (resolvent dC.conclusion dD.conclusion x) = some C' at hC'
      cases hCrest : restrictClause ρ dC.conclusion with
      | none =>
        cases hDrest : restrictClause ρ dD.conclusion with
        | none =>
          have hnone :=
            restrictClause_resolvent_none_of_parents_none ρ x hCrest hDrest
          rw [hnone] at hC'
          cases hC'
        | some D' =>
          obtain ⟨E, dE, hEsub, hEsz, hEwd, hEfat⟩ := ihD (C' := D') hDrest
          have hDR : D' ⊆ C' :=
            restrict_sub_of_left_killed (C := dC.conclusion) (D := dD.conclusion)
              ρ x hx hCrest hDrest hC'
          refine ⟨E, dE, Subset.trans hEsub hDR, Nat.le_trans hEsz ?_,
            Nat.le_trans hEwd ?_, fun t => Nat.le_trans (hEfat t) ?_⟩
          · change dD.size ≤ dC.size + dD.size + 1; omega
          · simp only [Derivation.width]; omega
          · simp only [Derivation.fatCount]; omega
      | some Cparent =>
        cases hDrest : restrictClause ρ dD.conclusion with
        | none =>
          obtain ⟨E, dE, hEsub, hEsz, hEwd, hEfat⟩ := ihC (C' := Cparent) hCrest
          have hCR : Cparent ⊆ C' :=
            restrict_sub_of_right_killed (C := dC.conclusion) (D := dD.conclusion)
              ρ x hnx hCrest hDrest hC'
          refine ⟨E, dE, Subset.trans hEsub hCR, Nat.le_trans hEsz ?_,
            Nat.le_trans hEwd ?_, fun t => Nat.le_trans (hEfat t) ?_⟩
          · change dC.size ≤ dC.size + dD.size + 1; omega
          · simp only [Derivation.width]; omega
          · simp only [Derivation.fatCount]; omega
        | some Dparent =>
          have hxun : ρ x = none := by
            cases hρ : ρ x with
            | none => rfl
            | some b =>
              cases b
              · have : restrictClause ρ dD.conclusion = none :=
                  (restrictClause_eq_none_iff ρ _).mpr
                    ⟨⟨x, false⟩, hnx, by simp [hρ]⟩
                rw [this] at hDrest
                cases hDrest
              · have : restrictClause ρ dC.conclusion = none :=
                  (restrictClause_eq_none_iff ρ _).mpr
                    ⟨⟨x, true⟩, hx, by simp [hρ]⟩
                rw [this] at hCrest
                cases hCrest
          obtain ⟨hReq, _, _⟩ :=
            restrict_resolvent_of_both_some (C := dC.conclusion) (D := dD.conclusion)
              ρ x hx hnx hCrest hDrest hxun
          have hC'eq : C' = resolvent Cparent Dparent x :=
            Option.some.inj (hC'.symm.trans hReq)
          obtain ⟨E1, d1, h1, hs1, hw1, hf1⟩ := ihC (C' := Cparent) hCrest
          obtain ⟨E2, d2, h2, hs2, hw2, hf2⟩ := ihD (C' := Dparent) hDrest
          by_cases hE1x : (⟨x, true⟩ : Literal) ∈ E1
          · by_cases hE2x : (⟨x, false⟩ : Literal) ∈ E2
            · refine ⟨resolvent E1 E2 x, Derivation.res x d1 d2 hE1x hE2x, ?_, ?_, ?_, ?_⟩
              · intro l hl
                have := resolvent_subset_of_subset (x := x) h1 h2 hl
                simpa [hC'eq] using this
              · change d1.size + d2.size + 1 ≤ dC.size + dD.size + 1; omega
              · -- Width bound via subclause cards and IH widths.
                have hRsub := resolvent_subset_of_subset (x := x)
                  (h1.trans (restrictClause_subset hCrest))
                  (h2.trans (restrictClause_subset hDrest))
                have hRcard := card_le_of_subset hRsub
                simp only [Derivation.width]
                refine max_le ?_ (hRcard.trans (le_max_right _ _))
                exact max_le (hw1.trans (le_max_left _ _))
                  (hw2.trans (le_max_right _ _)) |>.trans (le_max_left _ _)
              · intro t
                have hRsub := resolvent_subset_of_subset (x := x)
                  (h1.trans (restrictClause_subset hCrest))
                  (h2.trans (restrictClause_subset hDrest))
                have hRcard := card_le_of_subset hRsub
                -- `d1.conclusion` is definitionally `E1` (and likewise for `d2`).
                change d1.fatCount t + d2.fatCount t +
                    (if (resolvent E1 E2 x).card > t then 1 else 0) ≤
                  dC.fatCount t + dD.fatCount t +
                    (if (resolvent dC.conclusion dD.conclusion x).card > t then 1 else 0)
                by_cases hfatE : (resolvent E1 E2 x).card > t
                · have hfatR :
                      (resolvent dC.conclusion dD.conclusion x).card > t :=
                    Nat.lt_of_lt_of_le hfatE hRcard
                  simp only [hfatE, hfatR, ↓reduceIte]
                  have h12 := Nat.add_le_add (hf1 t) (hf2 t)
                  omega
                · simp only [hfatE, ↓reduceIte]
                  by_cases hfatR :
                      (resolvent dC.conclusion dD.conclusion x).card > t
                  · simp only [hfatR, ↓reduceIte]
                    have h12 := Nat.add_le_add (hf1 t) (hf2 t)
                    omega
                  · simp only [hfatR, ↓reduceIte]
                    have h12 := Nat.add_le_add (hf1 t) (hf2 t)
                    omega
            · refine ⟨E2, d2, ?_, Nat.le_trans hs2 ?_, Nat.le_trans hw2 ?_,
                fun t => Nat.le_trans (hf2 t) ?_⟩
              · intro l hl
                have hlD : l ∈ Dparent := h2 hl
                have hlne : l ≠ ⟨x, false⟩ := fun heq => hE2x (heq ▸ hl)
                rw [hC'eq]
                exact mem_union_right _ (mem_erase.mpr ⟨hlne, hlD⟩)
              · change dD.size ≤ dC.size + dD.size + 1; omega
              · simp only [Derivation.width]; omega
              · simp only [Derivation.fatCount]; omega
          · refine ⟨E1, d1, ?_, Nat.le_trans hs1 ?_, Nat.le_trans hw1 ?_,
              fun t => Nat.le_trans (hf1 t) ?_⟩
            · intro l hl
              have hlC : l ∈ Cparent := h1 hl
              have hlne : l ≠ ⟨x, true⟩ := fun heq => hE1x (heq ▸ hl)
              rw [hC'eq]
              exact mem_union_left _ (mem_erase.mpr ⟨hlne, hlC⟩)
            · change dC.size ≤ dC.size + dD.size + 1; omega
            · simp only [Derivation.width]; omega
            · simp only [Derivation.fatCount]; omega

/-- Size, width, and fat-count nonincreasing transport of a refutation. -/
theorem exists_restrict_refutation_width (ρ : ℕ → Option Bool) {F : CNF}
    (d : Derivation F (∅ : Clause)) :
    ∃ d' : Derivation (restrictCNF ρ F) (∅ : Clause),
      d'.size ≤ d.size ∧ d'.width ≤ d.width ∧ ∀ t, d'.fatCount t ≤ d.fatCount t := by
  obtain ⟨D, d', hsub, hsz, hwd, hfat⟩ :=
    exists_derivation_restrict_width ρ d (restrictClause_empty ρ)
  have hD : D = ∅ := Subset.antisymm hsub (empty_subset _)
  subst hD
  exact ⟨d', hsz, hwd, hfat⟩

end SATurday.ProofComplexity
