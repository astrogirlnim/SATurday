import Theory.ProofComplexity.Width

/-!
# Ben-Sasson and Wigderson Size versus Width (Ladder Rung R2)

Discrete `fatShrink` / `fatSteps` measures, kill-lit fat drop, and the core
`bsw_width_of_fatCount` induction (Ben-Sasson and Wigderson 2001).

LOG: R2 BSW size-width core induction
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

/-! ## Monotonicity of fatShrink / fatSteps -/

/-- Larger denominator yields a smaller natural quotient. -/
private theorem div_le_div_of_le_denominator {k N1 N2 : ℕ}
    (hN1 : 0 < N1) (hN : N1 ≤ N2) : k / N2 ≤ k / N1 := by
  have hmul : (k / N2) * N1 ≤ k := by
    have h1 : N1 * (k / N2) ≤ N2 * (k / N2) := Nat.mul_le_mul_right _ hN
    have h2 : N2 * (k / N2) ≤ k := by simpa [Nat.mul_comm] using Nat.mul_div_le k N2
    simpa [Nat.mul_comm] using h1.trans h2
  exact (Nat.le_div_iff_mul_le hN1).mpr hmul

/-- Larger literal budget removes fewer fat nodes in one averaging step. -/
theorem fatShrink_mono_N {N1 N2 t m : ℕ} (hN1 : 0 < N1) (hN : N1 ≤ N2) :
    fatShrink N1 t m ≤ fatShrink N2 t m := by
  simp only [fatShrink]
  exact Nat.sub_le_sub_left
    (Nat.add_le_add_right (div_le_div_of_le_denominator (k := t * m) hN1 hN) 1) _

/-- One-step monotonicity of `fatShrink` in the count when `t < N`. -/
theorem fatShrink_le_fatShrink_succ {N t m : ℕ} (ht : t < N) :
    fatShrink N t m ≤ fatShrink N t (m + 1) := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt ht
  simp only [fatShrink]
  have hdiv : t * (m + 1) / N ≤ t * m / N + 1 := by
    have hx := Nat.add_div (a := t * m) (b := t) hNpos
    have htN : t / N = 0 := Nat.div_eq_of_lt ht
    have hmul : t * (m + 1) = t * m + t := Nat.mul_succ t m
    rw [hmul, hx, htN]
    split_ifs <;> omega
  omega

/-- `fatShrink` is monotone in the count under `t < N`. -/
theorem fatShrink_mono_m {N t : ℕ} (ht : t < N) {m1 m2 : ℕ}
    (hle : m1 ≤ m2) : fatShrink N t m1 ≤ fatShrink N t m2 := by
  induction hle with
  | refl => exact le_rfl
  | step h ih => exact ih.trans (fatShrink_le_fatShrink_succ ht)

/-- `fatSteps` is monotone in the count when `t < N`. -/
theorem fatSteps_mono_m {N t : ℕ} (ht : t < N) {m1 m2 : ℕ}
    (hle : m1 ≤ m2) : fatSteps N t m1 ≤ fatSteps N t m2 := by
  induction m2 using Nat.strong_induction_on generalizing m1 with
  | h m2 ih =>
    by_cases hm2 : 0 < m2
    · by_cases hm1 : 0 < m1
      · rw [fatSteps_of_pos N t m1 hm1, fatSteps_of_pos N t m2 hm2]
        exact Nat.add_le_add_left
          (ih (fatShrink N t m2) (fatShrink_lt hm2) (fatShrink_mono_m ht hle)) 1
      · simp [Nat.eq_zero_of_not_pos hm1, fatSteps_zero]
    · have hm2z : m2 = 0 := Nat.eq_zero_of_not_pos hm2
      have hm1z : m1 = 0 := Nat.eq_zero_of_le_zero (hm2z ▸ hle)
      simp [hm1z, hm2z, fatSteps_zero]

theorem mem_cnfVars_of_mem_cnfLits {F : CNF} {l : Literal}
    (hl : l ∈ cnfLits F) : l.var ∈ cnfVars F := by
  simp only [cnfLits, mem_biUnion] at hl
  obtain ⟨v, hv, hlit⟩ := hl
  simp only [mem_insert, mem_singleton] at hlit
  rcases hlit with h | h
  · exact (congrArg Literal.var h) ▸ hv
  · exact (congrArg Literal.var h) ▸ hv

theorem cnfLits_card_le_of_vars_subset {F G : CNF}
    (h : cnfVars F ⊆ cnfVars G) :
    (cnfLits F).card ≤ (cnfLits G).card := by
  simp only [cnfLits_card]
  exact Nat.mul_le_mul_left 2 (card_le_card h)

/-! ## False-branch hypothesis recovery -/

private theorem filter_assignOne_eq_var_ne {x : ℕ} {b : Bool} {C0 D : Clause}
    (hres : restrictClause (assignOne x b) C0 = some D) :
    D = C0.filter fun lit => lit.var ≠ x := by
  have h := ((restrictClause_eq_some_iff (assignOne x b) C0 D).mp hres).2
  rw [h]
  ext lit
  simp [assignOne]

/-- Every clause of the false-branch restriction is width-bounded derivable
from `F` once the complementary unit `negLit l` is in hand. -/
theorem exists_derivation_false_branch_clause {F : CNF} (l : Literal)
    {U : Clause} (dU : Derivation F U) (hU : U = {negLit l})
    {D : Clause} (hD : D ∈ restrictCNF (assignOne l.var (!l.pos)) F) :
    ∃ d : Derivation F D, d.width ≤ max (cnfWidth F) dU.width := by
  obtain ⟨C0, hC0, hres⟩ := (mem_restrictCNF_iff (assignOne l.var (!l.pos)) F D).mp hD
  have hDsub : D ⊆ C0 := restrictClause_subset hres
  have hpre : C0 ⊆ insert l D := by
    simpa using
      (assignOne_preimage_subset (x := l.var) (b := !l.pos) hres)
  have hnsat :
      ∀ lit ∈ C0, assignOne l.var (!l.pos) lit.var ≠ some lit.pos :=
    ((restrictClause_eq_some_iff _ C0 D).mp hres).1
  by_cases hlC0 : l ∈ C0
  · rcases l with ⟨x, p⟩
    change U = {⟨x, !p⟩} at hU
    change (⟨x, p⟩ : Literal) ∈ C0 at hlC0
    have hopp : (⟨x, !p⟩ : Literal) ∉ C0 := fun hop =>
      hnsat _ hop (by simp [assignOne])
    have hDeq := filter_assignOne_eq_var_ne (x := x) (b := !p) hres
    have herase : D = C0.erase ⟨x, p⟩ := by
      ext lit
      simp only [hDeq, mem_filter, mem_erase]
      constructor
      · rintro ⟨hlit, hvar⟩
        exact ⟨fun heq => hvar (by cases lit; cases heq; rfl), hlit⟩
      · rintro ⟨hne, hlit⟩
        refine ⟨hlit, fun hv => ?_⟩
        have : lit.pos = p ∨ lit.pos = !p := by
          cases lit.pos <;> cases p <;> simp
        rcases this with hp | hp
        · exact hne (by cases lit; simp_all [hp, hv])
        · have : lit = ⟨x, !p⟩ := by cases lit; simp_all [hp, hv]
          exact hopp (this ▸ hlit)
    cases p
    · have hx : (⟨x, true⟩ : Literal) ∈ U := by simp [hU]
      have hnx : (⟨x, false⟩ : Literal) ∈ C0 := hlC0
      have hReq : resolvent U C0 x = D := by
        rw [herase, hU]; simp [resolvent, erase_singleton]
      rw [← hReq]
      refine ⟨Derivation.res x dU (Derivation.hyp C0 hC0) hx hnx, ?_⟩
      simp only [Derivation.width]
      have hC0le := Derivation.width_hyp_le_cnfWidth hC0
      have hRle : (resolvent U C0 x).card ≤ cnfWidth F := by
        have hsub : resolvent U C0 x ⊆ C0 := by
          intro lit hl
          have : lit ∈ C0.erase ⟨x, false⟩ := by
            simpa [resolvent, hU, erase_singleton] using hl
          exact (mem_erase.mp this).2
        exact (card_le_card hsub).trans hC0le
      exact max_le (max_le (le_max_right _ _) (hC0le.trans (le_max_left _ _)))
        (hRle.trans (le_max_left _ _))
    · have hx : (⟨x, true⟩ : Literal) ∈ C0 := hlC0
      have hnx : (⟨x, false⟩ : Literal) ∈ U := by simp [hU]
      have hReq : resolvent C0 U x = D := by
        rw [herase, hU]; simp [resolvent, erase_singleton]
      rw [← hReq]
      refine ⟨Derivation.res x (Derivation.hyp C0 hC0) dU hx hnx, ?_⟩
      simp only [Derivation.width]
      have hC0le := Derivation.width_hyp_le_cnfWidth hC0
      have hRle : (resolvent C0 U x).card ≤ cnfWidth F := by
        have hsub : resolvent C0 U x ⊆ C0 := by
          intro lit hl
          have : lit ∈ C0.erase ⟨x, true⟩ := by
            simpa [resolvent, hU, erase_singleton] using hl
          exact (mem_erase.mp this).2
        exact (card_le_card hsub).trans hC0le
      exact max_le (max_le (hC0le.trans (le_max_left _ _)) (le_max_right _ _))
        (hRle.trans (le_max_left _ _))
  · have hEq : D = C0 :=
      Subset.antisymm hDsub fun a ha => by
        have h := hpre ha
        simp only [mem_insert] at h
        rcases h with rfl | hDmem
        · exact absurd ha hlC0
        · exact hDmem
    rw [hEq]
    exact ⟨Derivation.hyp C0 hC0,
      (Derivation.width_hyp_le_cnfWidth hC0).trans (le_max_left _ _)⟩

/-! ## Core BSW width-of-fatCount tradeoff -/

/-- Strengthened induction: literal budget `N` may over-approximate `(cnfLits F).card`. -/
theorem bsw_width_of_fatCount_aux (N t : ℕ) :
    ∀ (m nv : ℕ) (F : CNF),
      (cnfVars F).card = nv →
      (cnfLits F).card ≤ N →
      ∀ (d : Derivation F (∅ : Clause)),
        d.fatCount t = m →
        ∃ d' : Derivation F (∅ : Clause),
          d'.width ≤ cnfWidth F + t + fatSteps N t m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    intro nv
    induction nv using Nat.strong_induction_on with
    | h nv ihnv =>
      intro F hnv hN d hfat
      by_cases hmpos : 0 < m
      · have hmF : 0 < d.fatCount t := by simpa [hfat] using hmpos
        have htF : t < (cnfLits F).card := by
          by_contra hge
          have : d.fatCount t = 0 :=
            Derivation.fatCount_eq_zero_of_lits_le d (Nat.not_lt.mp hge)
          omega
        have htN : t < N := lt_of_lt_of_le htF hN
        have hNF_pos : 0 < (cnfLits F).card := Nat.zero_lt_of_lt htF
        obtain ⟨l, hlits, hpop⟩ := exists_popular_literal d t hmF
        obtain ⟨d1, _hwd1, hfat1⟩ :=
          fatCount_kill_le_fatShrink l d t (by simpa [hfat] using hpop)
        have hN1 :
            (cnfLits (restrictCNF (assignOne l.var l.pos) F)).card ≤ N :=
          (cnfLits_card_le_of_vars_subset
            (cnfVars_restrictCNF_subset _ F)).trans hN
        have hm1le : d1.fatCount t ≤ fatShrink (cnfLits F).card t m := by
          simpa [hfat] using hfat1
        have hm1lt : d1.fatCount t < m :=
          lt_of_le_of_lt hm1le
            (fatShrink_lt (N := (cnfLits F).card) (t := t) hmpos)
        obtain ⟨d1n, hw1n⟩ :=
          ihm (d1.fatCount t) hm1lt
            (cnfVars (restrictCNF (assignOne l.var l.pos) F)).card
            (restrictCNF (assignOne l.var l.pos) F) rfl hN1 d1 rfl
        obtain ⟨U, dU, hUsub, hUwd⟩ := exists_derivation_add_lit d1n
        have hstep :
            fatSteps N t m = 1 + fatSteps N t (fatShrink N t m) :=
          fatSteps_of_pos N t m hmpos
        have hw1n' :
            d1n.width ≤ cnfWidth F + t + fatSteps N t (fatShrink N t m) := by
          have hmono :
              fatSteps N t (d1.fatCount t) ≤
                fatSteps N t (fatShrink N t m) :=
            fatSteps_mono_m htN
              (hm1le.trans (fatShrink_mono_N hNF_pos hN))
          calc
            d1n.width
                ≤ cnfWidth (restrictCNF (assignOne l.var l.pos) F) + t +
                    fatSteps N t (d1.fatCount t) := hw1n
            _ ≤ cnfWidth F + t + fatSteps N t (d1.fatCount t) :=
              Nat.add_le_add_right
                (Nat.add_le_add_right (cnfWidth_restrictCNF_le _ F) t) _
            _ ≤ cnfWidth F + t + fatSteps N t (fatShrink N t m) :=
              Nat.add_le_add_left hmono _
        have hUbound :
            dU.width ≤ cnfWidth F + t + fatSteps N t m := by
          have hmax :
              max (cnfWidth F) (d1n.width + 1) ≤
                cnfWidth F + t + fatSteps N t m := by
            refine max_le (by omega) ?_
            have : d1n.width + 1 ≤
                cnfWidth F + t + fatSteps N t (fatShrink N t m) + 1 := by
              omega
            rw [hstep]; omega
          exact hUwd.trans hmax
        by_cases hUempty : U = (∅ : Clause)
        · subst hUempty
          exact ⟨dU, hUbound⟩
        · have hUsing : U = {negLit l} := by
            obtain ⟨a, ha⟩ := nonempty_of_ne_empty hUempty
            have ha' : a = negLit l := by
              have := hUsub ha
              simpa [mem_singleton] using this
            refine Subset.antisymm ?_ (singleton_subset_iff.mpr (ha' ▸ ha))
            intro z hz
            have := hUsub hz
            simpa [mem_singleton] using this
          obtain ⟨d0, _hsz0, _hwd0, hfat0⟩ :=
            exists_restrict_refutation_width (assignOne l.var (!l.pos)) d
          have hN0 :
              (cnfLits (restrictCNF (assignOne l.var (!l.pos)) F)).card ≤ N :=
            (cnfLits_card_le_of_vars_subset
              (cnfVars_restrictCNF_subset _ F)).trans hN
          have hm0le : d0.fatCount t ≤ m := by simpa [hfat] using hfat0 t
          have hvar : l.var ∈ cnfVars F := mem_cnfVars_of_mem_cnfLits hlits
          have hnv0lt :
              (cnfVars (restrictCNF (assignOne l.var (!l.pos)) F)).card < nv := by
            have hss :=
              cnfVars_restrictCNF_ssubset_assignOne (F := F) (!l.pos) hvar
            simpa [hnv] using card_lt_card hss
          by_cases hm0lt : d0.fatCount t < m
          · obtain ⟨d0n, hw0n⟩ :=
              ihm (d0.fatCount t) hm0lt
                (cnfVars (restrictCNF (assignOne l.var (!l.pos)) F)).card
                (restrictCNF (assignOne l.var (!l.pos)) F) rfl hN0 d0 rfl
            have hw0bound :
                d0n.width ≤ cnfWidth F + t + fatSteps N t m := by
              calc
                d0n.width
                    ≤ cnfWidth (restrictCNF (assignOne l.var (!l.pos)) F) +
                        t + fatSteps N t (d0.fatCount t) := hw0n
                _ ≤ cnfWidth F + t + fatSteps N t (d0.fatCount t) :=
                  Nat.add_le_add_right
                    (Nat.add_le_add_right (cnfWidth_restrictCNF_le _ F) t) _
                _ ≤ cnfWidth F + t + fatSteps N t m :=
                  Nat.add_le_add_left (fatSteps_mono_m htN hm0le) _
            have hAll :
                ∀ C ∈ restrictCNF (assignOne l.var (!l.pos)) F,
                  ∃ e : Derivation F C,
                    e.width ≤ max (cnfWidth F) dU.width :=
              fun C hC =>
                exists_derivation_false_branch_clause l dU hUsing hC
            obtain ⟨dG, hwG⟩ :=
              exists_derivation_graft_width
                (max (cnfWidth F) dU.width) hAll d0n
            exact ⟨dG,
              hwG.trans (max_le (max_le (by omega) hUbound) hw0bound)⟩
          · have hm0eq : d0.fatCount t = m :=
              le_antisymm hm0le (Nat.not_lt.mp hm0lt)
            obtain ⟨d0n, hw⟩ :=
              ihnv (cnfVars (restrictCNF (assignOne l.var (!l.pos)) F)).card
                hnv0lt (restrictCNF (assignOne l.var (!l.pos)) F) rfl hN0 d0
                hm0eq
            have hw0n :
                d0n.width ≤
                  cnfWidth (restrictCNF (assignOne l.var (!l.pos)) F) + t +
                    fatSteps N t (d0.fatCount t) := by
              simpa [hm0eq] using hw
            have hw0bound :
                d0n.width ≤ cnfWidth F + t + fatSteps N t m := by
              calc
                d0n.width
                    ≤ cnfWidth (restrictCNF (assignOne l.var (!l.pos)) F) +
                        t + fatSteps N t (d0.fatCount t) := hw0n
                _ ≤ cnfWidth F + t + fatSteps N t (d0.fatCount t) :=
                  Nat.add_le_add_right
                    (Nat.add_le_add_right (cnfWidth_restrictCNF_le _ F) t) _
                _ ≤ cnfWidth F + t + fatSteps N t m :=
                  Nat.add_le_add_left (fatSteps_mono_m htN hm0le) _
            have hAll :
                ∀ C ∈ restrictCNF (assignOne l.var (!l.pos)) F,
                  ∃ e : Derivation F C,
                    e.width ≤ max (cnfWidth F) dU.width :=
              fun C hC =>
                exists_derivation_false_branch_clause l dU hUsing hC
            obtain ⟨dG, hwG⟩ :=
              exists_derivation_graft_width
                (max (cnfWidth F) dU.width) hAll d0n
            exact ⟨dG,
              hwG.trans (max_le (max_le (by omega) hUbound) hw0bound)⟩
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmpos
        subst hm0
        refine ⟨d, ?_⟩
        have hw := width_le_of_fatCount_zero d t hfat
        simp only [fatSteps_zero, Nat.add_zero]
        exact hw.trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

/-- Ben-Sasson and Wigderson: a refutation of fat count `m` yields a refutation
whose width is at most `cnfWidth F + t + fatSteps (2 * |vars|) t m`. -/
theorem bsw_width_of_fatCount (F : CNF) (t : ℕ)
    (d : Derivation F (∅ : Clause)) :
    ∃ d' : Derivation F (∅ : Clause),
      d'.width ≤
        cnfWidth F + t +
          fatSteps (2 * (cnfVars F).card) t (d.fatCount t) := by
  have hN : (cnfLits F).card ≤ 2 * (cnfVars F).card := by
    simp [cnfLits_card]
  obtain ⟨d', hw⟩ :=
    bsw_width_of_fatCount_aux (2 * (cnfVars F).card) t
      (d.fatCount t) (cnfVars F).card F rfl hN d rfl
  exact ⟨d', hw⟩


/-! ## Rate arithmetic: fatSteps versus log -/

/-- Averaging block length: about `N / t` steps suffice to cut the fat count. -/
def fatBlock (N t : ℕ) : ℕ := N / t + 1

/-- Under `0 < t`, the literal budget fits in one averaging block. -/
theorem le_mul_fatBlock {N t : ℕ} (ht : 0 < t) : N ≤ t * fatBlock N t :=
  (Nat.lt_mul_div_succ N ht).le

/-- Pigeon arithmetic: `m / fatBlock ≤ t * m / N`. -/
theorem div_fatBlock_le_mul_div {N t m : ℕ} (ht : 0 < t) (hNt : t ≤ N) :
    m / fatBlock N t ≤ t * m / N := by
  set B := fatBlock N t with hB
  have hNpos : 0 < N := Nat.zero_lt_of_lt (lt_of_lt_of_le ht hNt)
  have hNB : N ≤ t * B := by simpa [hB] using le_mul_fatBlock ht
  refine (Nat.le_div_iff_mul_le hNpos).mpr ?_
  calc
    (m / B) * N ≤ (m / B) * (t * B) := Nat.mul_le_mul_left _ hNB
    _ = t * (m / B * B) := by ring
    _ ≤ t * m := Nat.mul_le_mul_left t (Nat.div_mul_le_self m B)

/-- Iterating `fatShrink` never increases the count. -/
theorem iterate_fatShrink_le (N t m k : ℕ) :
    (fatShrink N t)^[k] m ≤ m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (fatShrink_le_self N t _).trans ih

/-- More shrink iterations yields a smaller or equal count. -/
theorem iterate_fatShrink_anti (N t m : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    (fatShrink N t)^[k] m ≤ (fatShrink N t)^[j] m := by
  induction hjk with
  | refl => exact le_rfl
  | step h ih =>
    rw [Function.iterate_succ_apply']
    exact (fatShrink_le_self N t _).trans ih

/-- `fatSteps` pays at most the iterate length plus the residual count's steps. -/
theorem fatSteps_le_add_iterate (N t m k : ℕ) :
    fatSteps N t m ≤ k + fatSteps N t ((fatShrink N t)^[k] m) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    by_cases hm : 0 < m
    · rw [fatSteps_of_pos N t m hm, Function.iterate_succ_apply]
      have := ih (fatShrink N t m)
      omega
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst hm0
      have hfix : fatShrink N t 0 = 0 := by simp [fatShrink]
      simp [fatSteps_zero, Function.iterate_fixed hfix]

/-- When `t < N` and `cur > 0`, one shrink removes at least `t*cur/N + 1`. -/
private theorem fatShrink_drop_lt {N t cur : ℕ}
    (htN : t < N) (hcur : 0 < cur) :
    t * cur / N + 1 ≤ cur - fatShrink N t cur := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt htN
  have hlt : t * cur / N < cur := by
    have hmul : t * cur < N * cur := Nat.mul_lt_mul_of_pos_right htN hcur
    exact Nat.div_lt_of_lt_mul hmul
  have hle : t * cur / N + 1 ≤ cur := Nat.succ_le_of_lt hlt
  simp only [fatShrink]
  omega

/-- Drop lower bound under `t < N` when the current count is at least `halfSucc`. -/
private theorem fatShrink_drop_of_half_ge {N t cur halfSucc : ℕ}
    (htN : t < N) (hcur : halfSucc ≤ cur) (hpos : 0 < halfSucc) :
    t * halfSucc / N + 1 ≤ cur - fatShrink N t cur := by
  have hcurpos : 0 < cur := lt_of_lt_of_le hpos hcur
  have hdrop := fatShrink_drop_lt (N := N) (t := t) (cur := cur) htN hcurpos
  have hle : t * halfSucc / N ≤ t * cur / N :=
    Nat.div_le_div_right (Nat.mul_le_mul_left t hcur)
  omega

/-- Block removal lower bound for `t < N`. -/
theorem fatBlock_mul_half_succ_div_ge {N t m : ℕ}
    (ht : 0 < t) (htN : t < N) :
    fatBlock N t * (t * (m / 2 + 1) / N + 1) ≥ m - m / 2 := by
  set B := fatBlock N t
  set a := m / 2 + 1
  have hNt : t ≤ N := le_of_lt htN
  have hdiv : a / B ≤ t * a / N := div_fatBlock_le_mul_div (m := a) ht hNt
  have hBpos : 0 < B := Nat.succ_pos _
  have h1 : B * (a / B + 1) ≤ B * (t * a / N + 1) :=
    Nat.mul_le_mul_left B (Nat.add_le_add_right hdiv 1)
  have h2 : a + 1 ≤ B * (a / B) + B := by
    have hdivmod : B * (a / B) + a % B = a := Nat.div_add_mod a B
    have hmod : a % B < B := Nat.mod_lt a hBpos
    omega
  have h3 : B * (a / B + 1) = B * (a / B) + B := by ring
  have h4 : m / 2 + 2 ≤ B * (a / B + 1) := by
    rw [h3]; simpa [a] using h2
  have h5 : m - m / 2 ≤ m / 2 + 1 := by omega
  omega

/-- Telescope under `t < N`. -/
private theorem fatShrink_iterate_drop_ge {N t m : ℕ}
    (htN : t < N) (k : ℕ)
    (hstay : ∀ j < k, m / 2 + 1 ≤ (fatShrink N t)^[j] m) :
    k * (t * (m / 2 + 1) / N + 1) ≤ m - (fatShrink N t)^[k] m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstay' : ∀ j < k, m / 2 + 1 ≤ (fatShrink N t)^[j] m :=
      fun j hj => hstay j (Nat.lt_succ_of_lt hj)
    have ihk := ih hstay'
    have hcur : m / 2 + 1 ≤ (fatShrink N t)^[k] m := hstay k (Nat.lt_succ_self _)
    have hdrop :=
      fatShrink_drop_of_half_ge (N := N) (t := t)
        (cur := (fatShrink N t)^[k] m) (halfSucc := m / 2 + 1) htN hcur
        (Nat.succ_pos _)
    have hiter :
        (fatShrink N t)^[k + 1] m = fatShrink N t ((fatShrink N t)^[k] m) :=
      Function.iterate_succ_apply' _ _ _
    have hle1 : (fatShrink N t)^[k + 1] m ≤ (fatShrink N t)^[k] m := by
      rw [hiter]; exact fatShrink_le_self _ _ _
    have hle0 : (fatShrink N t)^[k] m ≤ m := iterate_fatShrink_le N t m k
    calc
      (k + 1) * (t * (m / 2 + 1) / N + 1)
          = k * (t * (m / 2 + 1) / N + 1) + (t * (m / 2 + 1) / N + 1) := by
            ring
      _ ≤ (m - (fatShrink N t)^[k] m) +
            ((fatShrink N t)^[k] m - fatShrink N t ((fatShrink N t)^[k] m)) :=
          Nat.add_le_add ihk hdrop
      _ = m - fatShrink N t ((fatShrink N t)^[k] m) := by omega
      _ = m - (fatShrink N t)^[k + 1] m := by rw [hiter]

/-- When `t = N`, one shrink wipes the count. -/
private theorem fatShrink_eq_zero_of_t_eq_N {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    fatShrink N N m = 0 := by
  simp only [fatShrink]
  have : N * m / N = m := by rw [Nat.mul_comm, Nat.mul_div_left m hN]
  omega

/-- After one averaging block the fat count is at most half. -/
theorem fatShrink_iterate_fatBlock_le_half {N t m : ℕ}
    (ht : 0 < t) (hNt : t ≤ N) :
    (fatShrink N t)^[fatBlock N t] m ≤ m / 2 := by
  set B := fatBlock N t
  by_cases hteq : t = N
  · -- With `t = N`, a single shrink reaches 0.
    by_cases hm : m = 0
    · subst hm
      have hfix : fatShrink N t 0 = 0 := by simp [fatShrink]
      simp [Function.iterate_fixed hfix]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have hNpos : 0 < N := lt_of_lt_of_le ht hNt
      have h1 : fatShrink N t m = 0 := by
        simpa [hteq] using fatShrink_eq_zero_of_t_eq_N hNpos hmpos
      have hB : B = 2 := by
        simp only [B, fatBlock, hteq, Nat.div_self hNpos]
      have hfix : fatShrink N t 0 = 0 := by simp [fatShrink]
      have hstep0 : (fatShrink N t)^[1] m = 0 := by
        rw [Function.iterate_one, h1]
      calc
        (fatShrink N t)^[B] m = (fatShrink N t)^[2] m := by rw [hB]
        _ = (fatShrink N t)^[1 + 1] m := rfl
        _ = (fatShrink N t)^[1] ((fatShrink N t)^[1] m) := by
              rw [Function.iterate_add_apply]
        _ = (fatShrink N t)^[1] 0 := by rw [hstep0]
        _ = 0 := by rw [Function.iterate_one, hfix]
        _ ≤ m / 2 := Nat.zero_le _
  · -- `t < N`: additive block argument
    have htN : t < N := Nat.lt_of_le_of_ne hNt hteq
    by_contra hgt
    have hmB : m / 2 + 1 ≤ (fatShrink N t)^[B] m := by omega
    have hm_ge : m / 2 + 1 ≤ m :=
      hmB.trans (iterate_fatShrink_le N t m B)
    have hstay : ∀ j ≤ B, m / 2 + 1 ≤ (fatShrink N t)^[j] m := by
      intro j hj
      exact hmB.trans (iterate_fatShrink_anti N t m hj)
    have hstay' : ∀ j < B, m / 2 + 1 ≤ (fatShrink N t)^[j] m :=
      fun j hj => hstay j (le_of_lt hj)
    have hrm := fatShrink_iterate_drop_ge (N := N) (t := t) (m := m) htN B hstay'
    have hrm' := fatBlock_mul_half_succ_div_ge (N := N) (t := t) (m := m) ht htN
    have hupper : m - (fatShrink N t)^[B] m ≤ m - (m / 2 + 1) :=
      Nat.sub_le_sub_left hmB _
    have hge : m - m / 2 ≤ B * (t * (m / 2 + 1) / N + 1) := hrm'
    have hle : B * (t * (m / 2 + 1) / N + 1) ≤ m - (m / 2 + 1) :=
      hrm.trans hupper
    have hchain : m - m / 2 ≤ m - (m / 2 + 1) := hge.trans hle
    have hstrict : m - (m / 2 + 1) + 1 = m - m / 2 := by omega
    omega

/-- `fatSteps N t m ≤ fatBlock N t * (Nat.log 2 m + 1)`. -/
theorem fatSteps_le_log {N t m : ℕ} (ht : 0 < t) (hNt : t ≤ N) :
    fatSteps N t m ≤ fatBlock N t * (Nat.log 2 m + 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst hm; simp [fatSteps_zero]
    · set B := fatBlock N t
      have hiter :=
        fatShrink_iterate_fatBlock_le_half (N := N) (t := t) (m := m) ht hNt
      set m' := (fatShrink N t)^[B] m
      have hm'le : m' ≤ m / 2 := by simpa [m', B] using hiter
      have hsteps : fatSteps N t m ≤ B + fatSteps N t m' := by
        simpa [m', B] using fatSteps_le_add_iterate N t m B
      by_cases hm'0 : m' = 0
      · have hsteps0 : fatSteps N t m ≤ B := by
          simpa [hm'0, fatSteps_zero] using hsteps
        exact hsteps0.trans (Nat.le_mul_of_pos_right B (Nat.succ_pos _))
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hm2lt : m / 2 < m := Nat.div_lt_self hmpos (by decide : 1 < 2)
        have hm'lt : m' < m := lt_of_le_of_lt hm'le hm2lt
        have ih' : fatSteps N t m' ≤ B * (Nat.log 2 m' + 1) := by
          simpa [B] using ih m' hm'lt
        have hm2le : 2 ≤ m := by
          have : 0 < m' := Nat.pos_of_ne_zero hm'0
          have : 1 ≤ m / 2 := by omega
          omega
        have hlogm : 1 ≤ Nat.log 2 m :=
          Nat.log_pos (by decide : 1 < 2) hm2le
        have hlog' : Nat.log 2 m' + 1 ≤ Nat.log 2 m := by
          have hle : Nat.log 2 m' ≤ Nat.log 2 (m / 2) :=
            Nat.log_mono_right hm'le
          have hdiv : Nat.log 2 (m / 2) = Nat.log 2 m - 1 := Nat.log_div_base 2 m
          omega
        calc
          fatSteps N t m ≤ B + fatSteps N t m' := hsteps
          _ ≤ B + B * (Nat.log 2 m' + 1) := Nat.add_le_add_left ih' _
          _ = B * (1 + (Nat.log 2 m' + 1)) := by ring
          _ ≤ B * (Nat.log 2 m + 1) := Nat.mul_le_mul_left B (by omega)

/-- Explicit rate constant reserved for the size corollary packaging. -/
def bswRateConst : ℕ := 24

/-- Every derivation has positive size. -/
theorem Derivation.size_pos {F : CNF} {C : Clause} (d : Derivation F C) :
    0 < d.size := by
  induction d with
  | hyp _ _ => exact Nat.succ_pos _
  | res _ _ _ _ _ ihC ihD =>
    simp only [Derivation.size]
    omega

/-- Width-to-log-size intermediate form of the rate packaging. -/
theorem bsw_width_log_bound (F : CNF) (W : ℕ)
    (hW : ∀ d : Derivation F (∅ : Clause), W ≤ d.width)
    (d : Derivation F (∅ : Clause))
    (t : ℕ) (ht : 0 < t)
    (htN : t ≤ 2 * (cnfVars F).card) :
    W ≤ cnfWidth F + t +
      fatBlock (2 * (cnfVars F).card) t * (Nat.log 2 d.size + 1) := by
  set N := 2 * (cnfVars F).card
  obtain ⟨d', hw⟩ := bsw_width_of_fatCount F t d
  have hWd' := hW d'
  have h1 : W ≤ cnfWidth F + t + fatSteps N t (d.fatCount t) := by
    simpa [N] using hWd'.trans hw
  have hlog := fatSteps_le_log (N := N) (t := t) (m := d.fatCount t) ht htN
  have hfat : d.fatCount t ≤ d.size := d.fatCount_le_size t
  have hlogS :
      fatSteps N t (d.fatCount t) ≤
        fatBlock N t * (Nat.log 2 d.size + 1) :=
    hlog.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_mono_right hfat)))
  exact h1.trans (Nat.add_le_add_left hlogS _)

/-! ## Size lower bound rate corollary -/

/-- Every line of a derivation uses only literals from `cnfLits F`. -/
theorem Derivation.width_le_cnfLits_card {F : CNF} {C : Clause}
    (d : Derivation F C) : d.width ≤ (cnfLits F).card := by
  induction d with
  | hyp C hC =>
      simpa [Derivation.width] using
        Derivation.concl_card_le_cnfLits (Derivation.hyp C hC)
  | res x dC dD hx hnx ihC ihD =>
      have hres :=
        Derivation.concl_card_le_cnfLits (Derivation.res x dC dD hx hnx)
      simp only [Derivation.width]
      exact max_le (max_le ihC ihD) hres

/-- With `t = Δ / 2` and `Δ ≤ N`, the packed literal budget is at most `4 N`. -/
theorem delta_mul_fatBlock_le {N Δ : ℕ} (hΔN : Δ ≤ N) (ht : 0 < Δ / 2) :
    Δ * fatBlock N (Δ / 2) ≤ 4 * N := by
  set t := Δ / 2
  have htpos : 0 < t := ht
  have hmul_div : t * (N / t) ≤ N := Nat.mul_div_le N t
  have hcases : Δ = 2 * t ∨ Δ = 2 * t + 1 := by omega
  simp only [fatBlock]
  rcases hcases with hEq | hEq
  · -- Even gap: `Δ * (N/t + 1) ≤ 3 N ≤ 4 N`.
    have hrewrite : Δ * (N / t + 1) = 2 * (t * (N / t)) + 2 * t := by
      rw [hEq]; ring
    have hstep :
        2 * (t * (N / t)) + 2 * t ≤ 2 * N + Δ := by
      have h2 : 2 * (t * (N / t)) ≤ 2 * N := Nat.mul_le_mul_left 2 hmul_div
      have hΔ : 2 * t = Δ := by omega
      omega
    have h3 : 2 * N + Δ ≤ 3 * N := by omega
    exact (hrewrite.le.trans hstep).trans (h3.trans (by omega))
  · -- Odd gap: one extra `N / t ≤ N`.
    have hNt : N / t ≤ N := Nat.div_le_self N t
    have hrewrite :
        Δ * (N / t + 1) = 2 * (t * (N / t)) + N / t + (2 * t + 1) := by
      rw [hEq]; ring
    have hstep :
        2 * (t * (N / t)) + N / t + (2 * t + 1) ≤ 3 * N + Δ := by
      have h2 : 2 * (t * (N / t)) ≤ 2 * N := Nat.mul_le_mul_left 2 hmul_div
      have hΔ : 2 * t + 1 = Δ := by omega
      omega
    have h4 : 3 * N + Δ ≤ 4 * N := by omega
    exact (hrewrite.le.trans hstep).trans h4

/-- From the width-log inequality at half gap: `Δ^2 ≤ 8 N L`. -/
theorem bsw_delta_sq_le_of_width_log {N Δ L : ℕ}
    (hΔN : Δ ≤ N) (ht : 0 < Δ / 2)
    (hmain : Δ ≤ Δ / 2 + fatBlock N (Δ / 2) * L) :
    Δ * Δ ≤ 8 * N * L := by
  set t := Δ / 2
  have hdt : Δ - t ≤ fatBlock N t * L := by omega
  have hprod : Δ * (Δ - t) ≤ Δ * (fatBlock N t * L) :=
    Nat.mul_le_mul_left Δ hdt
  have hpack : Δ * fatBlock N t ≤ 4 * N :=
    delta_mul_fatBlock_le (N := N) (Δ := Δ) hΔN ht
  have hbound : Δ * (Δ - t) ≤ 4 * N * L := by
    calc
      Δ * (Δ - t) ≤ Δ * (fatBlock N t * L) := hprod
      _ = (Δ * fatBlock N t) * L := by ring
      _ ≤ (4 * N) * L := Nat.mul_le_mul_right L hpack
  have hdouble : Δ * Δ ≤ 2 * (Δ * (Δ - t)) := by
    have hle : Δ ≤ 2 * (Δ - t) := by omega
    calc
      Δ * Δ ≤ Δ * (2 * (Δ - t)) := Nat.mul_le_mul_left Δ hle
      _ = 2 * (Δ * (Δ - t)) := by ring
  calc
    Δ * Δ ≤ 2 * (Δ * (Δ - t)) := hdouble
    _ ≤ 2 * (4 * N * L) := Nat.mul_le_mul_left 2 hbound
    _ = 8 * N * L := by ring

/-- Rate corollary: width lower bound implies exponential size at `bswRateConst = 24`. -/
theorem bsw_size_lower_bound (F : CNF) (W : ℕ)
    (hW : ∀ d : Derivation F (∅ : Clause), W ≤ d.width)
    (d : Derivation F (∅ : Clause)) :
    2 ^ ((W - cnfWidth F) * (W - cnfWidth F) /
          (bswRateConst * (cnfVars F).card)) ≤ d.size := by
  set n := (cnfVars F).card
  set N := 2 * n
  set Δ := W - cnfWidth F
  set S := d.size
  set L := Nat.log 2 S + 1
  set e := Δ * Δ / (bswRateConst * n)
  have hSpos : 0 < S := d.size_pos
  have hSne : S ≠ 0 := Nat.pos_iff_ne_zero.mp hSpos
  by_cases he0 : e = 0
  · -- Exponent zero: claim is `1 ≤ S`.
    simpa [e, he0] using Nat.succ_le_of_lt hSpos
  -- Nontrivial exponent forces `Δ ≥ 2` and a positive half-gap.
  have hΔge : 2 ≤ Δ := by
    by_contra hlt
    have hΔle : Δ ≤ 1 := by omega
    have : e = 0 := by
      by_cases hn0 : n = 0
      · simp [e, bswRateConst, hn0]
      · have hnum : Δ * Δ ≤ 1 := Nat.mul_le_mul hΔle hΔle
        have hlt' : Δ * Δ < bswRateConst * n := by
          simp only [bswRateConst]
          omega
        exact Nat.div_eq_of_lt hlt'
    exact he0 this
  have ht : 0 < Δ / 2 := by omega
  have hwcard : d.width ≤ N := by
    simpa [N, n, cnfLits_card] using d.width_le_cnfLits_card
  have hW_le_N : W ≤ N := (hW d).trans hwcard
  have hΔN : Δ ≤ N := (Nat.sub_le W (cnfWidth F)).trans hW_le_N
  have htN : Δ / 2 ≤ N := (Nat.div_le_self Δ 2).trans hΔN
  have hlog :=
    bsw_width_log_bound F W hW d (Δ / 2) ht (by simpa [N] using htN)
  have hmain : Δ ≤ Δ / 2 + fatBlock N (Δ / 2) * L := by
    have : W ≤ cnfWidth F + Δ / 2 + fatBlock N (Δ / 2) * L := by
      simpa [N, L, S] using hlog
    omega
  have hsq : Δ * Δ ≤ 8 * N * L :=
    bsw_delta_sq_le_of_width_log (N := N) (Δ := Δ) (L := L) hΔN ht hmain
  have hsq' : Δ * Δ ≤ 16 * n * L := by
    have : 8 * N * L = 16 * n * L := by simp only [N]; ring
    simpa [this] using hsq
  have hnpos : 0 < n := by
    have : 2 ≤ N := hΔge.trans hΔN
    omega
  have hden : bswRateConst * n = 24 * n := by simp [bswRateConst]
  have he_le_log : e ≤ Nat.log 2 S := by
    by_cases hlog2 : 2 ≤ Nat.log 2 S
    · -- Large log: `16 (log + 1) ≤ 24 log`.
      have hcoeff : 16 * L ≤ 24 * Nat.log 2 S := by
        simp only [L]; omega
      have hnum24 : Δ * Δ ≤ (24 * n) * Nat.log 2 S := by
        calc
          Δ * Δ ≤ 16 * n * L := hsq'
          _ = n * (16 * L) := by ring
          _ ≤ n * (24 * Nat.log 2 S) := Nat.mul_le_mul_left n hcoeff
          _ = (24 * n) * Nat.log 2 S := by ring
      -- `div_le_of_le_mul`: `m ≤ k * q → m / k ≤ q` with `k = 24 n`.
      have := Nat.div_le_of_le_mul hnum24
      simpa [e, hden] using this
    · -- Small log (`≤ 1`): `Δ^2 ≤ 32 n` forces `e ≤ 1`, and `e ≠ 0` forces `log = 1`.
      have hlogle : Nat.log 2 S ≤ 1 := by omega
      have hLle : L ≤ 2 := by simp only [L]; omega
      have hnum32 : Δ * Δ ≤ 32 * n := by
        calc
          Δ * Δ ≤ 16 * n * L := hsq'
          _ ≤ 16 * n * 2 := Nat.mul_le_mul_left _ hLle
          _ = 32 * n := by ring
      have he_le1 : e ≤ 1 := by
        have hdiv : Δ * Δ / (24 * n) ≤ 32 * n / (24 * n) :=
          Nat.div_le_div_right hnum32
        have h32 : 32 * n / (24 * n) = 1 := by
          calc
            32 * n / (24 * n) = n * 32 / (n * 24) := by ring_nf
            _ = 32 / 24 := Nat.mul_div_mul_left 32 24 hnpos
            _ = 1 := by decide
        simpa [e, hden] using hdiv.trans_eq h32
      have hlogge1 : 1 ≤ Nat.log 2 S := by
        by_contra h
        have hlog0 : Nat.log 2 S = 0 := by omega
        have hL1 : L = 1 := by simp [L, hlog0]
        have hnum16 : Δ * Δ ≤ 16 * n := by simpa [hL1] using hsq'
        have hlt : Δ * Δ < 24 * n := by omega
        have : e = 0 := by
          simpa [e, hden] using Nat.div_eq_of_lt hlt
        exact he0 this
      omega
  exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) hSne).1 he_le_log

/-! ## Non vacuity witness: implication chain family -/

/-- Positive unit clause `{x k}`. -/
def chainUnitPos (k : ℕ) : Clause := {⟨k, true⟩}

/-- Negative unit clause `{¬x k}`. -/
def chainUnitNeg (k : ℕ) : Clause := {⟨k, false⟩}

/-- Implication step `{¬x k, x (k+1)}`. -/
def chainImpl (k : ℕ) : Clause := {⟨k, false⟩, ⟨k + 1, true⟩}

/-- Implication chain CNF on variables `0..n`:
`{x0}`, `{¬x0,x1}`, ..., `{¬x(n-1),xn}`, `{¬xn}`. -/
def chainCNF (n : ℕ) : CNF :=
  insert (chainUnitPos 0)
    (insert (chainUnitNeg n) ((Finset.range n).image chainImpl))

theorem chainUnitPos_mem (n : ℕ) : chainUnitPos 0 ∈ chainCNF n :=
  mem_insert_self _ _

theorem chainUnitNeg_mem (n : ℕ) : chainUnitNeg n ∈ chainCNF n :=
  mem_insert_of_mem (mem_insert_self _ _)

theorem chainImpl_mem (n k : ℕ) (hk : k < n) : chainImpl k ∈ chainCNF n := by
  refine mem_insert_of_mem (mem_insert_of_mem ?_)
  exact mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩

theorem resolvent_chain_step (k : ℕ) :
    resolvent (chainUnitPos k) (chainImpl k) k = chainUnitPos (k + 1) := by
  ext l
  simp only [resolvent, chainUnitPos, chainImpl, mem_union, mem_erase, mem_insert,
    mem_singleton]
  constructor
  · intro h
    rcases h with ⟨hne, rfl⟩ | ⟨hne, h⟩
    · exact absurd rfl hne
    · rcases h with rfl | rfl
      · exact absurd rfl hne
      · rfl
  · intro h
    subst h
    right
    exact ⟨by
      intro heq
      exact Bool.noConfusion (congrArg Literal.pos heq), Or.inr rfl⟩

theorem resolvent_chain_end (n : ℕ) :
    resolvent (chainUnitPos n) (chainUnitNeg n) n = (∅ : Clause) := by
  ext l
  simp [resolvent, chainUnitPos, chainUnitNeg]

/-- Unit propagation derives `{x k}` from `chainCNF n` for every `k ≤ n`. -/
def chainDeriveUnitPos (n : ℕ) :
    (k : ℕ) → k ≤ n → Derivation (chainCNF n) (chainUnitPos k)
  | 0, _ => Derivation.hyp (chainUnitPos 0) (chainUnitPos_mem n)
  | k + 1, hk =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      let dPrev := chainDeriveUnitPos n k hk'
      let dImpl := Derivation.hyp (chainImpl k) (chainImpl_mem n k hkn)
      have hx : (⟨k, true⟩ : Literal) ∈ chainUnitPos k := by
        simp [chainUnitPos]
      have hnx : (⟨k, false⟩ : Literal) ∈ chainImpl k := by
        simp [chainImpl]
      (resolvent_chain_step k) ▸ Derivation.res k dPrev dImpl hx hnx

/-- Explicit unit propagation refutation of `chainCNF n`. -/
def chainRefutation (n : ℕ) : Derivation (chainCNF n) (∅ : Clause) :=
  let dPos := chainDeriveUnitPos n n le_rfl
  let dNeg := Derivation.hyp (chainUnitNeg n) (chainUnitNeg_mem n)
  have hx : (⟨n, true⟩ : Literal) ∈ chainUnitPos n := by
    simp [chainUnitPos]
  have hnx : (⟨n, false⟩ : Literal) ∈ chainUnitNeg n := by
    simp [chainUnitNeg]
  (resolvent_chain_end n) ▸ Derivation.res n dPos dNeg hx hnx

theorem chainUnitPos_card (k : ℕ) : (chainUnitPos k).card = 1 := by
  simp [chainUnitPos]

theorem chainUnitNeg_card (k : ℕ) : (chainUnitNeg k).card = 1 := by
  simp [chainUnitNeg]

theorem chainImpl_card (k : ℕ) : (chainImpl k).card = 2 := by
  have hne : (⟨k, false⟩ : Literal) ≠ ⟨k + 1, true⟩ := by
    intro h
    exact Nat.ne_of_lt (Nat.lt_succ_self k) (congrArg Literal.var h)
  simp [chainImpl, card_insert_of_notMem, hne]

/-- Casting a derivation along an equality of conclusions preserves width. -/
theorem Derivation.width_eq_cast {F : CNF} {C D : Clause}
    (h : C = D) (d : Derivation F C) :
    (h ▸ d).width = d.width := by
  cases h
  rfl

/-- Casting preserves fat counts. -/
theorem Derivation.fatCount_eq_cast {F : CNF} {C D : Clause}
    (h : C = D) (d : Derivation F C) (t : ℕ) :
    (h ▸ d).fatCount t = d.fatCount t := by
  cases h
  rfl

theorem chainDeriveUnitPos_width (n k : ℕ) (hk : k ≤ n) :
    (chainDeriveUnitPos n k hk).width ≤ 2 := by
  induction k with
  | zero =>
      simp only [chainDeriveUnitPos, Derivation.width, chainUnitPos_card]
      norm_num
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      -- Unfold the succ clause of the definition.
      change
          ((resolvent_chain_step k) ▸
            Derivation.res k (chainDeriveUnitPos n k hk')
              (Derivation.hyp (chainImpl k) (chainImpl_mem n k hkn))
              (by simp [chainUnitPos]) (by simp [chainImpl])).width ≤ 2
      rw [Derivation.width_eq_cast]
      simp only [Derivation.width]
      have hwPrev := ih hk'
      have hwImpl : (Derivation.hyp (chainImpl k) (chainImpl_mem n k hkn)).width ≤ 2 := by
        simp [Derivation.width, chainImpl_card]
      have hRes : (resolvent (chainUnitPos k) (chainImpl k) k).card ≤ 2 := by
        rw [resolvent_chain_step, chainUnitPos_card]
        norm_num
      exact max_le (max_le hwPrev hwImpl) hRes

theorem chainRefutation_width_le (n : ℕ) : (chainRefutation n).width ≤ 2 := by
  simp only [chainRefutation]
  rw [Derivation.width_eq_cast]
  simp only [Derivation.width]
  have hwPos := chainDeriveUnitPos_width n n le_rfl
  have hwNeg : (Derivation.hyp (chainUnitNeg n) (chainUnitNeg_mem n)).width ≤ 2 := by
    simp [Derivation.width, chainUnitNeg_card]
  have hRes : (resolvent (chainUnitPos n) (chainUnitNeg n) n).card ≤ 2 := by
    rw [resolvent_chain_end]
    simp
  exact max_le (max_le hwPos hwNeg) hRes

/-- Width at most `t` forces zero fat count above `t`. -/
theorem Derivation.fatCount_eq_zero_of_width_le {F : CNF} {C : Clause}
    (d : Derivation F C) {t : ℕ} (h : d.width ≤ t) : d.fatCount t = 0 := by
  induction d with
  | hyp C hC =>
      simp only [Derivation.fatCount, Derivation.width] at h ⊢
      have : ¬ C.card > t := Nat.not_lt.mpr h
      simp [this]
  | res x dC dD hx hnx ihC ihD =>
      simp only [Derivation.fatCount, Derivation.width] at h ⊢
      have hC : dC.width ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) h)
      have hD : dD.width ≤ t :=
        le_trans (le_max_right _ _) (le_trans (le_max_left _ _) h)
      have hR : (resolvent dC.conclusion dD.conclusion x).card ≤ t :=
        le_trans (le_max_right _ _) h
      simp [ihC hC, ihD hD, Nat.not_lt.mpr hR]

theorem chainRefutation_fatCount_eq_zero (n t : ℕ) (ht : 2 ≤ t) :
    (chainRefutation n).fatCount t = 0 :=
  Derivation.fatCount_eq_zero_of_width_le (chainRefutation n)
    ((chainRefutation_width_le n).trans ht)

theorem chainCNF_clause_card_le (n : ℕ) {C : Clause} (hC : C ∈ chainCNF n) :
    C.card ≤ 2 := by
  simp only [chainCNF] at hC
  rcases mem_insert.mp hC with hEq | hC
  · rw [hEq, chainUnitPos_card]; norm_num
  · rcases mem_insert.mp hC with hEq | hC
    · rw [hEq, chainUnitNeg_card]; norm_num
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hC
      exact (chainImpl_card k).le

theorem chainCNF_cnfWidth_le (n : ℕ) : cnfWidth (chainCNF n) ≤ 2 :=
  Finset.sup_le fun C hC => chainCNF_clause_card_le n hC

theorem chainCNF_cnfWidth_of_pos (n : ℕ) (hn : 1 ≤ n) :
    cnfWidth (chainCNF n) = 2 := by
  refine le_antisymm (chainCNF_cnfWidth_le n) ?_
  have hmem : chainImpl 0 ∈ chainCNF n := chainImpl_mem n 0 hn
  exact (chainImpl_card 0).ge.trans (le_sup (f := Finset.card) hmem)

theorem mem_range_of_mem_cnfVars_chainCNF {n v : ℕ}
    (hv : v ∈ cnfVars (chainCNF n)) : v < n + 1 := by
  obtain ⟨C, hC, l, hl, rfl⟩ := mem_cnfVars.mp hv
  simp only [chainCNF] at hC
  rcases mem_insert.mp hC with hEq | hC
  · subst hEq
    simp only [chainUnitPos, mem_singleton] at hl
    cases hl
    exact Nat.succ_pos _
  · rcases mem_insert.mp hC with hEq | hC
    · subst hEq
      simp only [chainUnitNeg, mem_singleton] at hl
      cases hl
      exact Nat.lt_succ_self n
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp hC
      have hk' : k < n := mem_range.mp hk
      simp only [chainImpl, mem_insert, mem_singleton] at hl
      rcases hl with hEq | hEq
      · cases hEq; exact Nat.lt_succ_of_lt hk'
      · cases hEq; exact Nat.succ_lt_succ hk'

theorem mem_cnfVars_chainCNF_of_le (n v : ℕ) (hv : v ≤ n) :
    v ∈ cnfVars (chainCNF n) := by
  by_cases hv0 : v = 0
  · rw [hv0]
    exact mem_cnfVars.mpr
      ⟨chainUnitPos 0, chainUnitPos_mem n, ⟨0, true⟩, by simp [chainUnitPos], rfl⟩
  · by_cases hvn : v = n
    · rw [hvn]
      exact mem_cnfVars.mpr
        ⟨chainUnitNeg n, chainUnitNeg_mem n, ⟨n, false⟩, by simp [chainUnitNeg], rfl⟩
    · have hpred : v - 1 < n := by omega
      have hvEq : v = (v - 1) + 1 := by omega
      refine mem_cnfVars.mpr
        ⟨chainImpl (v - 1), chainImpl_mem n (v - 1) hpred, ⟨v, true⟩, ?_, rfl⟩
      simp only [chainImpl, mem_insert, mem_singleton]
      right
      exact congrArg (fun x => (⟨x, true⟩ : Literal)) hvEq ▸ rfl

theorem cnfVars_chainCNF (n : ℕ) :
    cnfVars (chainCNF n) = Finset.range (n + 1) := by
  ext v
  constructor
  · intro hv
    exact mem_range.mpr (mem_range_of_mem_cnfVars_chainCNF hv)
  · intro hv
    exact mem_cnfVars_chainCNF_of_le n v (Nat.lt_succ_iff.mp (mem_range.mp hv))

theorem cnfVars_chainCNF_card (n : ℕ) :
    (cnfVars (chainCNF n)).card = n + 1 := by
  simp [cnfVars_chainCNF]

/-- Satisfying assignment forces every chain variable true, contradicting the end unit. -/
theorem chainCNF_unsat (n : ℕ) : ¬Satisfiable (chainCNF n) := by
  rintro ⟨a, ha⟩
  have hforce : ∀ k ≤ n, a k = true := by
    intro k hk
    induction k with
    | zero =>
      obtain ⟨l, hl, hla⟩ := ha _ (chainUnitPos_mem n)
      simp only [chainUnitPos, mem_singleton] at hl
      cases hl
      simpa [litSat] using hla
    | succ k ih =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hak : a k = true := ih hk'
      obtain ⟨l, hl, hla⟩ := ha _ (chainImpl_mem n k hkn)
      simp only [chainImpl, mem_insert, mem_singleton] at hl
      rcases hl with hEq | hEq
      · cases hEq
        simp only [litSat] at hla
        exact False.elim (Bool.noConfusion (hla.symm.trans hak))
      · cases hEq
        simpa [litSat] using hla
  obtain ⟨l, hl, hla⟩ := ha _ (chainUnitNeg_mem n)
  simp only [chainUnitNeg, mem_singleton] at hl
  cases hl
  simp only [litSat] at hla
  exact Bool.noConfusion ((hforce n le_rfl).symm.trans hla)

theorem chainCNF_refutable (n : ℕ) : Refutable (chainCNF n) :=
  ⟨chainRefutation n⟩

/-- The BSW width bound on the chain witness is strictly below the trivial
`2 * |vars|` width ceiling for every `n ≥ 2`. -/
theorem bsw_bound_beats_trivial (n : ℕ) (hn : 2 ≤ n) :
    cnfWidth (chainCNF n) + (cnfVars (chainCNF n)).card +
        fatSteps (2 * (cnfVars (chainCNF n)).card) ((cnfVars (chainCNF n)).card)
          ((chainRefutation n).fatCount ((cnfVars (chainCNF n)).card)) <
      2 * (cnfVars (chainCNF n)).card := by
  have hvars : (cnfVars (chainCNF n)).card = n + 1 := cnfVars_chainCNF_card n
  have hw : cnfWidth (chainCNF n) = 2 :=
    chainCNF_cnfWidth_of_pos n (Nat.le_trans (by decide : 1 ≤ 2) hn)
  have ht2 : 2 ≤ n + 1 := by omega
  have hfat : (chainRefutation n).fatCount (n + 1) = 0 :=
    chainRefutation_fatCount_eq_zero n (n + 1) ht2
  have hbound :
      cnfWidth (chainCNF n) + (cnfVars (chainCNF n)).card +
          fatSteps (2 * (cnfVars (chainCNF n)).card) ((cnfVars (chainCNF n)).card)
            ((chainRefutation n).fatCount ((cnfVars (chainCNF n)).card)) =
        n + 3 := by
    rw [hw, hvars, hfat, fatSteps_zero]
    ring
  have hlt : n + 3 < 2 * (n + 1) := by omega
  have hR : 2 * (cnfVars (chainCNF n)).card = 2 * (n + 1) := by rw [hvars]
  exact hbound.symm ▸ (hR.symm ▸ hlt)

end SATurday.ProofComplexity
