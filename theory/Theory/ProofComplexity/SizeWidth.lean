import Theory.ProofComplexity.Width

/-!
# Ben-Sasson and Wigderson Size versus Width (Ladder Rung R2)

First SizeWidth cluster: discrete `fatShrink` / `fatSteps` measures and the
kill-lit restriction lemma that drops `fatLitCount` from the fat count.
The core `bsw_width_of_fatCount` induction is the next formalize cycle.

LOG: R2 BSW size-width measures and kill-lit transport
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Discrete fat-count recursion -/

/-- One averaging step: remove at least `t * m / N + 1` fat nodes. -/
def fatShrink (N t m : ℕ) : ℕ := m - (t * m / N + 1)

theorem fatShrink_lt {N t m : ℕ} (hm : 0 < m) : fatShrink N t m < m :=
  Nat.sub_lt hm (Nat.succ_pos _)

/-- Number of averaging steps until the fat count reaches zero. -/
def fatSteps (N t m : ℕ) : ℕ :=
  if h : 0 < m then
    have := fatShrink_lt (N := N) (t := t) h
    1 + fatSteps N t (fatShrink N t m)
  else
    0
termination_by m

theorem fatSteps_zero (N t : ℕ) : fatSteps N t 0 = 0 := by
  unfold fatSteps
  rfl

theorem fatSteps_of_pos (N t m : ℕ) (hm : 0 < m) :
    fatSteps N t m = 1 + fatSteps N t (fatShrink N t m) := by
  rw [fatSteps, dif_pos hm]

theorem fatShrink_le_self (N t m : ℕ) : fatShrink N t m ≤ m :=
  Nat.sub_le _ _

theorem Derivation.fatLitCount_le_fatCount (t : ℕ) (l : Literal)
    {F : CNF} {C : Clause} (d : Derivation F C) :
    d.fatLitCount t l ≤ d.fatCount t := by
  induction d with
  | hyp _ _ =>
      simp only [Derivation.fatLitCount, Derivation.fatCount]
      split_ifs <;> omega
  | res _ _ _ _ _ ihC ihD =>
      simp only [Derivation.fatLitCount, Derivation.fatCount]
      split_ifs <;> omega

theorem Derivation.concl_card_le_cnfLits {F : CNF} {C : Clause}
    (d : Derivation F C) : C.card ≤ (cnfLits F).card :=
  card_le_card fun _ hl => derivation_mem_cnfLits d hl

theorem Derivation.fatCount_eq_zero_of_lits_le {F : CNF} {C : Clause}
    (d : Derivation F C) {t : ℕ} (ht : (cnfLits F).card ≤ t) :
    d.fatCount t = 0 := by
  induction d with
  | hyp C hC =>
      simp only [Derivation.fatCount]
      have : ¬ C.card > t :=
        Nat.not_lt.mpr
          ((Derivation.concl_card_le_cnfLits (Derivation.hyp C hC)).trans ht)
      simp [this]
  | res x dC dD hx hnx ihC ihD =>
      simp only [Derivation.fatCount, ihC, ihD]
      have : ¬ (resolvent dC.conclusion dD.conclusion x).card > t :=
        Nat.not_lt.mpr
          ((Derivation.concl_card_le_cnfLits (Derivation.res x dC dD hx hnx)).trans ht)
      simp [this]

/-! ## Kill-lit restriction drops fatLitCount -/

private theorem mem_of_restrictClause_assignOne_none {x : ℕ} {b : Bool} {C : Clause}
    (h : restrictClause (assignOne x b) C = none) :
    (⟨x, b⟩ : Literal) ∈ C := by
  obtain ⟨lit, hl, hρ⟩ := (restrictClause_eq_none_iff _ _).mp h
  rcases lit with ⟨v, p⟩
  simp only [assignOne] at hρ
  by_cases hv : v = x
  · simp only [hv, ↓reduceIte, Option.some.injEq] at hρ
    subst hv
    simpa [hρ] using hl
  · simp only [hv, ↓reduceIte] at hρ
    -- hρ : none = some p after assignOne misses v
    nomatch hρ

private theorem fatLitCount_concl_pos {F : CNF} {C : Clause}
    (d : Derivation F C) (t : ℕ) (l : Literal)
    (hfat : C.card > t) (hl : l ∈ C) : 1 ≤ d.fatLitCount t l := by
  cases d with
  | hyp _ _ => simp [Derivation.fatLitCount, hfat, hl]
  | res x dC dD hx hnx =>
      simp only [Derivation.fatLitCount, Derivation.conclusion] at hfat hl ⊢
      simp [hfat, hl]

/-- Restriction killing `l` drops every fat node that contains `l`. -/
theorem exists_derivation_restrict_kill_lit {F : CNF} {C : Clause}
    (l : Literal) (d : Derivation F C) {C' : Clause}
    (hC' : restrictClause (assignOne l.var l.pos) C = some C') (t : ℕ) :
    ∃ D : Clause, ∃ d' : Derivation (restrictCNF (assignOne l.var l.pos) F) D,
      D ⊆ C' ∧ d'.width ≤ d.width ∧
        d'.fatCount t ≤ d.fatCount t - d.fatLitCount t l := by
  let ρ := assignOne l.var l.pos
  induction d generalizing C' with
  | hyp C hC =>
      have hlne : l ∉ C := by
        intro hl
        have hnone : restrictClause ρ C = none := by
          rcases l with ⟨v, p⟩
          exact (restrictClause_eq_none_iff _ _).mpr
            ⟨⟨v, p⟩, hl, by simp [ρ, assignOne]⟩
        rw [hnone] at hC'
        cases hC'
      refine ⟨C', Derivation.hyp C'
        ((mem_restrictCNF_iff ρ F C').mpr ⟨C, hC, hC'⟩), Subset.rfl, ?_, ?_⟩
      · exact card_le_of_subset (restrictClause_subset hC')
      · change
            (if C'.card > t then 1 else 0) ≤
              (if C.card > t then 1 else 0) -
                (if C.card > t ∧ l ∈ C then 1 else 0)
        have hle := card_le_of_subset (restrictClause_subset hC')
        simp only [hlne, and_false, ↓reduceIte, Nat.sub_zero]
        by_cases hfat : C.card > t
        · by_cases hfat' : C'.card > t <;> simp [hfat, hfat']
        · have : ¬ C'.card > t := mt (fun h => Nat.lt_of_lt_of_le h hle) hfat
          simp [hfat, this]
  | res x dC dD hx hnx ihC ihD =>
      change restrictClause ρ (resolvent dC.conclusion dD.conclusion x) = some C' at hC'
      cases hCrest : restrictClause ρ dC.conclusion with
      | none =>
        cases hDrest : restrictClause ρ dD.conclusion with
        | none =>
          have := restrictClause_resolvent_none_of_parents_none ρ x hCrest hDrest
          simp [this] at hC'
        | some D' =>
          obtain ⟨E, dE, hEsub, hEwd, hEfat⟩ := ihD hDrest
          have hDR := restrict_sub_of_left_killed (C := dC.conclusion)
            (D := dD.conclusion) ρ x hx hCrest hDrest hC'
          have hlC : l ∈ dC.conclusion := by
            rcases l with ⟨v, p⟩
            simpa [ρ] using mem_of_restrictClause_assignOne_none hCrest
          refine ⟨E, dE, hEsub.trans hDR,
            hEwd.trans (by simp only [Derivation.width]; omega), ?_⟩
          have hflC := Derivation.fatLitCount_le_fatCount t l dC
          have hflD := Derivation.fatLitCount_le_fatCount t l dD
          simp only [Derivation.fatCount, Derivation.fatLitCount]
          have hE := hEfat
          by_cases hfatC : dC.conclusion.card > t
          · have hpos := fatLitCount_concl_pos dC t l hfatC hlC
            split_ifs <;> omega
          · split_ifs <;> omega
      | some Cparent =>
        cases hDrest : restrictClause ρ dD.conclusion with
        | none =>
          obtain ⟨E, dE, hEsub, hEwd, hEfat⟩ := ihC hCrest
          have hCR := restrict_sub_of_right_killed (C := dC.conclusion)
            (D := dD.conclusion) ρ x hnx hCrest hDrest hC'
          refine ⟨E, dE, hEsub.trans hCR,
            hEwd.trans (by simp only [Derivation.width]; omega), ?_⟩
          have hflC := Derivation.fatLitCount_le_fatCount t l dC
          have hflD := Derivation.fatLitCount_le_fatCount t l dD
          simp only [Derivation.fatCount, Derivation.fatLitCount]
          have hE := hEfat
          split_ifs <;> omega
        | some Dparent =>
          have hxun : ρ x = none := by
            cases hρ : ρ x with
            | none => rfl
            | some b =>
              cases b
              · have : restrictClause ρ dD.conclusion = none :=
                  (restrictClause_eq_none_iff ρ _).mpr ⟨⟨x, false⟩, hnx, hρ⟩
                simp [this] at hDrest
              · have : restrictClause ρ dC.conclusion = none :=
                  (restrictClause_eq_none_iff ρ _).mpr ⟨⟨x, true⟩, hx, hρ⟩
                simp [this] at hCrest
          obtain ⟨hReq, _, _⟩ :=
            restrict_resolvent_of_both_some (C := dC.conclusion) (D := dD.conclusion)
              ρ x hx hnx hCrest hDrest hxun
          have hC'eq : C' = resolvent Cparent Dparent x :=
            Option.some.inj (hC'.symm.trans hReq)
          obtain ⟨E1, d1, h1, hw1, hf1⟩ := ihC hCrest
          obtain ⟨E2, d2, h2, hw2, hf2⟩ := ihD hDrest
          by_cases hE1x : (⟨x, true⟩ : Literal) ∈ E1
          · by_cases hE2x : (⟨x, false⟩ : Literal) ∈ E2
            · refine ⟨resolvent E1 E2 x, Derivation.res x d1 d2 hE1x hE2x, ?_, ?_, ?_⟩
              · exact fun lit hlit => hC'eq ▸ resolvent_subset_of_subset (x := x) h1 h2 hlit
              · have hRsub := resolvent_subset_of_subset (x := x)
                  (h1.trans (restrictClause_subset hCrest))
                  (h2.trans (restrictClause_subset hDrest))
                simp only [Derivation.width]
                exact max_le
                  ((max_le (hw1.trans (le_max_left _ _))
                    (hw2.trans (le_max_right _ _))).trans (le_max_left _ _))
                  ((card_le_of_subset hRsub).trans (le_max_right _ _))
              · have hlR : l ∉ resolvent dC.conclusion dD.conclusion x := by
                  intro hl
                  have : l ∈ dC.conclusion ∨ l ∈ dD.conclusion := by
                    simp only [resolvent, mem_union, mem_erase] at hl
                    rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> [exact Or.inl h; exact Or.inr h]
                  rcases this with hlC | hlD
                  · rcases l with ⟨v, p⟩
                    have : restrictClause ρ dC.conclusion = none :=
                      (restrictClause_eq_none_iff _ _).mpr
                        ⟨⟨v, p⟩, hlC, by simp [ρ, assignOne]⟩
                    simp [this] at hCrest
                  · rcases l with ⟨v, p⟩
                    have : restrictClause ρ dD.conclusion = none :=
                      (restrictClause_eq_none_iff _ _).mpr
                        ⟨⟨v, p⟩, hlD, by simp [ρ, assignOne]⟩
                    simp [this] at hDrest
                have hRcard := card_le_of_subset (resolvent_subset_of_subset (x := x)
                  (h1.trans (restrictClause_subset hCrest))
                  (h2.trans (restrictClause_subset hDrest)))
                have hflC := Derivation.fatLitCount_le_fatCount t l dC
                have hflD := Derivation.fatLitCount_le_fatCount t l dD
                -- Convert IH subtractions to additive form for omega
                have hf1' : d1.fatCount t + dC.fatLitCount t l ≤ dC.fatCount t :=
                  (Nat.le_sub_iff_add_le hflC).mp hf1
                have hf2' : d2.fatCount t + dD.fatLitCount t l ≤ dD.fatCount t :=
                  (Nat.le_sub_iff_add_le hflD).mp hf2
                -- Unfold the fat inequality and clear the kill-lit bit on the resolvent
                change
                  d1.fatCount t + d2.fatCount t +
                      (if (resolvent E1 E2 x).card > t then 1 else 0) ≤
                    (dC.fatCount t + dD.fatCount t +
                      (if (resolvent dC.conclusion dD.conclusion x).card > t then 1
                        else 0)) -
                    (dC.fatLitCount t l + dD.fatLitCount t l +
                      (if (resolvent dC.conclusion dD.conclusion x).card > t ∧
                          l ∈ resolvent dC.conclusion dD.conclusion x then 1
                        else 0))
                simp only [hlR, and_false, ↓reduceIte, Nat.add_zero]
                -- Turn the outer Nat subtraction into an additive comparison
                have hdrop :
                    dC.fatLitCount t l + dD.fatLitCount t l ≤
                      dC.fatCount t + dD.fatCount t +
                        (if (resolvent dC.conclusion dD.conclusion x).card > t then 1
                          else 0) := by
                  split_ifs <;> omega
                rw [Nat.le_sub_iff_add_le hdrop]
                by_cases hfatE : (resolvent E1 E2 x).card > t
                · have hfatR :
                      (resolvent dC.conclusion dD.conclusion x).card > t :=
                    Nat.lt_of_lt_of_le hfatE hRcard
                  simp only [hfatE, hfatR, ↓reduceIte]
                  omega
                · simp only [hfatE, ↓reduceIte]
                  split_ifs <;> omega
            · refine ⟨E2, d2,
                fun lit hlit => hC'eq ▸ mem_union_right _
                  (mem_erase.mpr ⟨fun heq => hE2x (heq ▸ hlit), h2 hlit⟩),
                hw2.trans (by simp only [Derivation.width]; omega), ?_⟩
              have hflC := Derivation.fatLitCount_le_fatCount t l dC
              have hflD := Derivation.fatLitCount_le_fatCount t l dD
              have hf2' : d2.fatCount t + dD.fatLitCount t l ≤ dD.fatCount t :=
                (Nat.le_sub_iff_add_le hflD).mp hf2
              simp only [Derivation.fatCount, Derivation.fatLitCount]
              split_ifs <;> omega
          · refine ⟨E1, d1,
              fun lit hlit => hC'eq ▸ mem_union_left _
                (mem_erase.mpr ⟨fun heq => hE1x (heq ▸ hlit), h1 hlit⟩),
              hw1.trans (by simp only [Derivation.width]; omega), ?_⟩
            have hflC := Derivation.fatLitCount_le_fatCount t l dC
            have hflD := Derivation.fatLitCount_le_fatCount t l dD
            have hf1' : d1.fatCount t + dC.fatLitCount t l ≤ dC.fatCount t :=
              (Nat.le_sub_iff_add_le hflC).mp hf1
            simp only [Derivation.fatCount, Derivation.fatLitCount]
            split_ifs <;> omega

theorem exists_restrict_refutation_kill_lit {F : CNF} (l : Literal)
    (d : Derivation F (∅ : Clause)) (t : ℕ) :
    ∃ d' : Derivation (restrictCNF (assignOne l.var l.pos) F) (∅ : Clause),
      d'.width ≤ d.width ∧
        d'.fatCount t ≤ d.fatCount t - d.fatLitCount t l := by
  obtain ⟨D, d', hsub, hwd, hfat⟩ :=
    exists_derivation_restrict_kill_lit l d (restrictClause_empty _) t
  obtain rfl : D = ∅ := Subset.antisymm hsub (empty_subset _)
  exact ⟨d', hwd, hfat⟩

/-- Kill-lit drop is at most a `fatShrink` step when `l` is popular. -/
theorem fatCount_kill_le_fatShrink {F : CNF} (l : Literal)
    (d : Derivation F (∅ : Clause)) (t : ℕ)
    (hpop : t * d.fatCount t / (cnfLits F).card + 1 ≤ d.fatLitCount t l) :
    ∃ d' : Derivation (restrictCNF (assignOne l.var l.pos) F) (∅ : Clause),
      d'.width ≤ d.width ∧
        d'.fatCount t ≤ fatShrink (cnfLits F).card t (d.fatCount t) := by
  obtain ⟨d', hwd, hfat⟩ := exists_restrict_refutation_kill_lit l d t
  refine ⟨d', hwd, hfat.trans ?_⟩
  have hfl := Derivation.fatLitCount_le_fatCount t l d
  simp only [fatShrink]
  omega

end SATurday.ProofComplexity
