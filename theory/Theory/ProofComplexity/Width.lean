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

/-! ## Averaging: popular literal among fat nodes -/

/-- Total cardinality mass of fat nodes (with multiplicity). -/
def Derivation.fatCardSum (t : ℕ) {F : CNF} : {C : Clause} → Derivation F C → ℕ
  | _, .hyp C _ => if C.card > t then C.card else 0
  | _, .res x dC dD _ _ =>
      dC.fatCardSum t + dD.fatCardSum t +
        if (resolvent dC.conclusion dD.conclusion x).card > t then
          (resolvent dC.conclusion dD.conclusion x).card
        else
          0

theorem Derivation.fatCardSum_ge_fatCount_mul (t : ℕ) {F : CNF} {C : Clause}
    (d : Derivation F C) :
    (t + 1) * d.fatCount t ≤ d.fatCardSum t := by
  induction d with
  | hyp C _ =>
      simp only [Derivation.fatCount, Derivation.fatCardSum]
      by_cases hfat : C.card > t
      · simp only [hfat, ↓reduceIte, Nat.mul_one]
        exact Nat.succ_le_of_lt hfat
      · simp [hfat]
  | res x dC dD _ _ ihC ihD =>
      simp only [Derivation.fatCount, Derivation.fatCardSum]
      by_cases hfat : (resolvent dC.conclusion dD.conclusion x).card > t
      · simp only [hfat, ↓reduceIte, Nat.mul_add, Nat.mul_one]
        have hR : t + 1 ≤ (resolvent dC.conclusion dD.conclusion x).card :=
          Nat.succ_le_of_lt hfat
        omega
      · simp only [hfat, ↓reduceIte, Nat.add_zero, Nat.mul_add]
        exact Nat.add_le_add ihC ihD

/-- Every literal of a derived clause lies in `cnfLits F`. -/
theorem derivation_mem_cnfLits {F : CNF} {C : Clause} (d : Derivation F C)
    {l : Literal} (hl : l ∈ C) : l ∈ cnfLits F := by
  have hv : l.var ∈ cnfVars F :=
    derivation_clauseVars_subset d (mem_image_of_mem Literal.var hl)
  rcases l with ⟨v, p⟩
  cases p <;> exact mem_biUnion.mpr ⟨v, hv, by simp [cnfLits]⟩

private theorem sum_ite_mem_eq_card {α : Type*} [DecidableEq α] (C S : Finset α)
    (h : C ⊆ S) :
    ∑ x ∈ S, (if x ∈ C then (1 : ℕ) else 0) = C.card :=
  (card_eq_sum_ite_mem C S h).symm

theorem Derivation.fatLitCount_sum_eq_fatCardSum (t : ℕ) {F : CNF} {C : Clause}
    (d : Derivation F C) :
    ∑ l ∈ cnfLits F, d.fatLitCount t l = d.fatCardSum t := by
  induction d with
  | hyp C hC =>
      simp only [Derivation.fatLitCount, Derivation.fatCardSum]
      by_cases hfat : C.card > t
      · have hsub : C ⊆ cnfLits F := fun l hl =>
          derivation_mem_cnfLits (Derivation.hyp C hC) hl
        simp only [hfat, ↓reduceIte, true_and]
        refine Eq.trans ?_ (sum_ite_mem_eq_card C (cnfLits F) hsub)
        refine sum_congr rfl fun l _ => ?_
        by_cases hl : l ∈ C <;> simp [hl]
      · simp only [hfat, ↓reduceIte, false_and]
        exact sum_eq_zero fun _ _ => rfl
  | res x dC dD hx hnx ihC ihD =>
      -- Unfold and split the sum into three additive pieces.
      let R := resolvent dC.conclusion dD.conclusion x
      show ∑ l ∈ cnfLits F,
          (dC.fatLitCount t l + dD.fatLitCount t l +
            if R.card > t ∧ l ∈ R then 1 else 0) =
        dC.fatCardSum t + dD.fatCardSum t + if R.card > t then R.card else 0
      have hsplit :
          ∑ l ∈ cnfLits F,
              (dC.fatLitCount t l + dD.fatLitCount t l +
                if R.card > t ∧ l ∈ R then 1 else 0) =
            (∑ l ∈ cnfLits F, dC.fatLitCount t l) +
              (∑ l ∈ cnfLits F, dD.fatLitCount t l) +
              ∑ l ∈ cnfLits F, (if R.card > t ∧ l ∈ R then 1 else 0) := by
        simp [sum_add_distrib]
      rw [hsplit, ihC, ihD]
      by_cases hfat : R.card > t
      · have hsub : R ⊆ cnfLits F := fun l hl =>
          derivation_mem_cnfLits (Derivation.res x dC dD hx hnx)
            (by simpa [R, Derivation.conclusion] using hl)
        simp only [hfat, true_and, ↓reduceIte]
        rw [sum_ite_mem_eq_card R (cnfLits F) hsub]
      · simp only [hfat, false_and, ↓reduceIte]
        rw [sum_eq_zero fun _ _ => rfl]

/-- BSW averaging: some literal hits at least `t * m / N + 1` fat nodes. -/
theorem exists_popular_literal {F : CNF} {C : Clause} (d : Derivation F C)
    (t : ℕ) (hm : 0 < d.fatCount t) :
    ∃ l ∈ cnfLits F,
      t * d.fatCount t / (cnfLits F).card + 1 ≤ d.fatLitCount t l := by
  classical
  set m := d.fatCount t with hm_def
  set N := (cnfLits F).card with hN_def
  have hsum := Derivation.fatLitCount_sum_eq_fatCardSum t d
  have hge := Derivation.fatCardSum_ge_fatCount_mul t d
  have hNpos : 0 < N := by
    by_contra hN
    have hempty : cnfLits F = ∅ := card_eq_zero.mp (Nat.eq_zero_of_not_pos hN)
    have hmulpos : 0 < (t + 1) * m := Nat.mul_pos (Nat.succ_pos t) hm
    have hmass : 0 < d.fatCardSum t := lt_of_lt_of_le hmulpos hge
    have hsum0 : d.fatCardSum t = 0 := by
      simpa [hempty, sum_empty] using hsum.symm
    omega
  have hne : (cnfLits F).Nonempty :=
    nonempty_of_ne_empty (mt card_eq_zero.mpr (ne_of_gt hNpos))
  obtain ⟨l, hl, hsup⟩ :=
    exists_mem_eq_sup (cnfLits F) hne (fun l => d.fatLitCount t l)
  have hmax :
      ∑ u ∈ cnfLits F, d.fatLitCount t u ≤ N * d.fatLitCount t l := by
    have := sum_le_card_nsmul (cnfLits F) (fun u => d.fatLitCount t u)
      (d.fatLitCount t l) (fun u hu => by
        have := le_sup (s := cnfLits F) (f := fun v => d.fatLitCount t v) hu
        exact hsup ▸ this)
    simpa [nsmul_eq_mul, N] using this
  refine ⟨l, hl, ?_⟩
  by_contra hlt
  have hle : d.fatLitCount t l ≤ t * m / N :=
    Nat.lt_succ_iff.mp (lt_of_not_ge hlt)
  have hchain1 : d.fatCardSum t ≤ N * (t * m / N) := by
    rw [← hsum]
    exact hmax.trans (Nat.mul_le_mul_left N hle)
  have hchain2 : N * (t * m / N) ≤ t * m := Nat.mul_div_le (t * m) N
  have hgt : t * m < (t + 1) * m :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self t) hm
  have hge' : (t + 1) * m ≤ d.fatCardSum t := by simpa [m] using hge
  omega

/-! ## Reintroducing a complementary literal (add_lit) -/

/-- Opposite polarity of a literal. -/
def negLit (l : Literal) : Literal := ⟨l.var, !l.pos⟩

theorem negLit_negLit (l : Literal) : negLit (negLit l) = l := by
  cases l
  simp [negLit]

/-- A survivor under `assignOne x b` is recovered (up to the complementary
unit) from its preimage clause in `F`. -/
theorem assignOne_preimage_subset {x : ℕ} {b : Bool} {C0 C' : Clause}
    (hres : restrictClause (assignOne x b) C0 = some C') :
    C0 ⊆ insert ⟨x, !b⟩ C' := by
  intro l hl
  obtain ⟨hnsat, hC'eq⟩ := (restrictClause_eq_some_iff (assignOne x b) C0 C').mp hres
  by_cases hvar : l.var = x
  · have hbne : some b ≠ some l.pos := by
      simpa [assignOne, hvar] using hnsat l hl
    have hpos : l.pos = !b := by
      cases b <;> cases lp : l.pos <;> simp_all
    rcases l with ⟨v, p⟩
    simp only at hvar hpos
    subst hvar
    simp [hpos]
  · have : l ∈ C' := by
      rw [hC'eq]
      exact mem_filter.mpr ⟨hl, by simp [assignOne, hvar]⟩
    exact mem_insert_of_mem this

private theorem add_lit_subset_resolvent {x y : ℕ} {b : Bool}
    {E1 E2 Cp Dp : Clause}
    (h1 : E1 ⊆ insert ⟨x, !b⟩ Cp) (h2 : E2 ⊆ insert ⟨x, !b⟩ Dp) :
    resolvent E1 E2 y ⊆ insert ⟨x, !b⟩ (resolvent Cp Dp y) := by
  intro l hl
  have hl' : l ∈ E1.erase ⟨y, true⟩ ∨ l ∈ E2.erase ⟨y, false⟩ :=
    (mem_union).mp (by simpa [resolvent] using hl)
  simp only [resolvent, mem_insert, mem_union, mem_erase]
  rcases hl' with hL | hR
  · obtain ⟨hlne, hl1⟩ := mem_erase.mp hL
    have h := h1 hl1
    simp only [mem_insert] at h
    rcases h with rfl | hlC
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hlne, hlC⟩)
  · obtain ⟨hlne, hl2⟩ := mem_erase.mp hR
    have h := h2 hl2
    simp only [mem_insert] at h
    rcases h with rfl | hlD
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hlne, hlD⟩)

/-- Lift a derivation over `restrictCNF (assignOne x b) F` back to `F`. -/
theorem exists_derivation_add_lit {F : CNF} {x : ℕ} {b : Bool} {C : Clause}
    (d : Derivation (restrictCNF (assignOne x b) F) C) :
    ∃ C' : Clause, ∃ d' : Derivation F C',
      C' ⊆ insert ⟨x, !b⟩ C ∧
        d'.width ≤ max (cnfWidth F) (d.width + 1) := by
  induction d with
  | hyp C hC =>
      obtain ⟨C0, hC0, hres⟩ := (mem_restrictCNF_iff (assignOne x b) F C).mp hC
      refine ⟨C0, Derivation.hyp C0 hC0, assignOne_preimage_subset hres, ?_⟩
      exact (Derivation.width_hyp_le_cnfWidth hC0).trans (le_max_left _ _)
  | res y dC dD hy hny ihC ihD =>
      obtain ⟨E1, d1, h1, hw1⟩ := ihC
      obtain ⟨E2, d2, h2, hw2⟩ := ihD
      have hy_ne : y ≠ x := by
        intro hxy
        have hv : y ∈ cnfVars (restrictCNF (assignOne x b) F) :=
          derivation_clauseVars_subset dC (mem_image_of_mem Literal.var hy)
        exact notMem_cnfVars_restrictCNF_of_assigned (by simp [assignOne])
          (hxy ▸ hv)
      by_cases hE1y : (⟨y, true⟩ : Literal) ∈ E1
      · by_cases hE2y : (⟨y, false⟩ : Literal) ∈ E2
        · refine ⟨resolvent E1 E2 y, Derivation.res y d1 d2 hE1y hE2y, ?sub, ?wd⟩
          case sub =>
            simpa [Derivation.conclusion] using
              add_lit_subset_resolvent (x := x) (y := y) (b := b) h1 h2
          case wd =>
            have hsub :=
              add_lit_subset_resolvent (x := x) (y := y) (b := b)
                (Cp := dC.conclusion) (Dp := dD.conclusion) h1 h2
            have hcard : (resolvent E1 E2 y).card ≤
                (resolvent dC.conclusion dD.conclusion y).card + 1 :=
              (card_le_card hsub).trans (card_insert_le _ _)
            set R := (resolvent dC.conclusion dD.conclusion y).card
            set M := max (max dC.width dD.width) R
            have hw1' : d1.width ≤ max (cnfWidth F) (M + 1) := by
              have : dC.width + 1 ≤ M + 1 :=
                Nat.add_le_add_right ((le_max_left _ _).trans (le_max_left _ _)) 1
              exact hw1.trans (max_le_max le_rfl this)
            have hw2' : d2.width ≤ max (cnfWidth F) (M + 1) := by
              have : dD.width + 1 ≤ M + 1 :=
                Nat.add_le_add_right ((le_max_right _ _).trans (le_max_left _ _)) 1
              exact hw2.trans (max_le_max le_rfl this)
            have hR' : (resolvent E1 E2 y).card ≤ max (cnfWidth F) (M + 1) := by
              have : R + 1 ≤ M + 1 := Nat.add_le_add_right (le_max_right _ _) 1
              exact hcard.trans (this.trans (le_max_right _ _))
            simp only [Derivation.width, M, R] at hw1' hw2' hR' ⊢
            exact max_le (max_le hw1' hw2') hR'
        · refine ⟨E2, d2, ?_, ?_⟩
          · intro l hl
            have h := h2 hl
            simp only [mem_insert] at h ⊢
            rcases h with rfl | hlD
            · exact Or.inl rfl
            · refine Or.inr (mem_union_right _ (mem_erase.mpr ⟨?_, hlD⟩))
              exact fun heq => hE2y (heq ▸ hl)
          · have : dD.width + 1 ≤
                max (max dC.width dD.width)
                    (resolvent dC.conclusion dD.conclusion y).card + 1 :=
              Nat.add_le_add_right ((le_max_right _ _).trans (le_max_left _ _)) 1
            exact hw2.trans (max_le_max le_rfl this)
      · refine ⟨E1, d1, ?_, ?_⟩
        · intro l hl
          have h := h1 hl
          simp only [mem_insert] at h ⊢
          rcases h with rfl | hlC
          · exact Or.inl rfl
          · refine Or.inr (mem_union_left _ (mem_erase.mpr ⟨?_, hlC⟩))
            exact fun heq => hE1y (heq ▸ hl)
        · have : dC.width + 1 ≤
              max (max dC.width dD.width)
                  (resolvent dC.conclusion dD.conclusion y).card + 1 :=
            Nat.add_le_add_right ((le_max_left _ _).trans (le_max_left _ _)) 1
          exact hw1.trans (max_le_max le_rfl this)

/-! ## Width-tracking hypothesis substitution (graft) -/

/-- Width-aware `derives_trans`: substitute a width-`W` derivation for every
hypothesis of `dG`. -/
theorem exists_derivation_graft_width {F G : CNF} {E : Clause} (W : ℕ)
    (hAll : ∀ C ∈ G, ∃ d : Derivation F C, d.width ≤ W)
    (dG : Derivation G E) :
    ∃ d : Derivation F E, d.width ≤ max W dG.width := by
  induction dG with
  | hyp C hC =>
      obtain ⟨d, hd⟩ := hAll C hC
      exact ⟨d, hd.trans (le_max_left _ _)⟩
  | res x dC dD hx hnx ihC ihD =>
      obtain ⟨eC, hwC⟩ := ihC
      obtain ⟨eD, hwD⟩ := ihD
      refine ⟨Derivation.res x eC eD hx hnx, ?_⟩
      set Rcard := (resolvent dC.conclusion dD.conclusion x).card
      set M := max (max dC.width dD.width) Rcard
      have hCbound : eC.width ≤ max W M := by
        have : dC.width ≤ M :=
          (le_max_left dC.width dD.width).trans (le_max_left _ _)
        exact hwC.trans (max_le_max le_rfl this)
      have hDbound : eD.width ≤ max W M := by
        have : dD.width ≤ M :=
          (le_max_right dC.width dD.width).trans (le_max_left _ _)
        exact hwD.trans (max_le_max le_rfl this)
      have hRbound : Rcard ≤ max W M := le_max_of_le_right (le_max_right _ _)
      simp only [Derivation.width, M, Rcard] at hCbound hDbound hRbound ⊢
      exact max_le (max_le hCbound hDbound) hRbound

end SATurday.ProofComplexity
