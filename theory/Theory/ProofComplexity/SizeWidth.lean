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

end SATurday.ProofComplexity
