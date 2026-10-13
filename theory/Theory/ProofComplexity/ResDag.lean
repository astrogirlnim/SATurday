import Theory.ProofComplexity.SizeWidth

/-!
# Dag-like resolution and the dag-like size-width relation (Ladder Rung R4, Phase 2.2, Khaniki)

`Derivation` of R0 is a proof tree (its `size` counts clause occurrences), so `SizeWidth` proves
Ben-Sasson and Wigderson for tree-like sizes. Here lines are shared: `DDer F S` says the finite
set `S` of clauses is built from the empty set by adding hypotheses and resolvents of two lines
already present, and the size is `S.card`, the number of distinct lines (dag-like size).
The BSW induction of `SizeWidth` is redone with the fat count `dfat t S = #{C ∈ S | t < |C|}`:
restriction of a dag is a dag with a subsuming line for every surviving line
(`DDer.restrict`), the popular literal is found by averaging over fat lines, and the output of the
induction is still an ordinary tree `Derivation` of small width (width does not see sharing).
Final form: `bsw_dag_size_lower_bound`, if every tree refutation has width at least `W` then every
dag refutation has at least `2 ^ ((W - cnfWidth F)^2 / (24 n))` lines (`n` = number of variables).

LOG: R4 Phase 2.2 ResDag module (dag-like BSW, for Khaniki's Res(lin F_p) bound)
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-- Dag-like resolution: a finite set of clauses built by adding hypotheses and resolvents of two
lines already present. -/
inductive DDer (F : CNF) : Finset Clause → Prop
  | empty : DDer F ∅
  | hyp {S : Finset Clause} (C : Clause) : DDer F S → C ∈ F → DDer F (insert C S)
  | res {S : Finset Clause} (x : ℕ) (C D : Clause) : DDer F S → C ∈ S → D ∈ S →
      (⟨x, true⟩ : Literal) ∈ C → (⟨x, false⟩ : Literal) ∈ D →
      DDer F (insert (resolvent C D x) S)

/-- Number of fat lines (more than `t` literals). -/
noncomputable def dfat (t : ℕ) (S : Finset Clause) : ℕ := (S.filter fun C => t < C.card).card

/-- Number of fat lines containing `l`. -/
noncomputable def dfatLit (t : ℕ) (l : Literal) (S : Finset Clause) : ℕ :=
  (S.filter fun C => t < C.card ∧ l ∈ C).card

theorem dfat_le_card (t : ℕ) (S : Finset Clause) : dfat t S ≤ S.card := card_filter_le _ _

theorem dfat_mono {t : ℕ} {S S' : Finset Clause} (h : S ⊆ S') : dfat t S ≤ dfat t S' :=
  card_le_card (filter_subset_filter _ h)

theorem dfat_insert_le (t : ℕ) (A : Clause) (S : Finset Clause) :
    dfat t (insert A S) ≤ dfat t S + (if t < A.card then 1 else 0) := by
  unfold dfat
  rw [filter_insert]
  split_ifs with h
  · exact (card_insert_le _ _).trans le_rfl
  · simp

theorem DDer.mono {F F' : CNF} (hF : F ⊆ F') {S : Finset Clause} (h : DDer F S) : DDer F' S := by
  induction h with
  | empty => exact DDer.empty
  | hyp C _ hC ih => exact DDer.hyp C ih (hF hC)
  | res x C D _ hC hD hx hnx ih => exact DDer.res x C D ih hC hD hx hnx

/-- A dag is a tree: every line has a tree derivation whose width is at most the widest line. -/
theorem DDer.to_tree {F : CNF} {S : Finset Clause} (h : DDer F S) :
    ∀ C ∈ S, ∃ d : Derivation F C, d.width ≤ S.sup Finset.card := by
  induction h with
  | empty => intro C hC; simp at hC
  | hyp C0 hS hC0 ih =>
    rename_i S
    intro C hC
    rcases mem_insert.1 hC with rfl | hC
    · exact ⟨Derivation.hyp C hC0, le_sup (f := Finset.card) (mem_insert_self _ _)⟩
    · obtain ⟨d, hd⟩ := ih C hC
      exact ⟨d, hd.trans (sup_mono (subset_insert _ _))⟩
  | res x C0 D0 hS hC0 hD0 hx hnx ih =>
    rename_i S
    intro C hC
    rcases mem_insert.1 hC with rfl | hC
    · obtain ⟨dC, hdC⟩ := ih C0 hC0
      obtain ⟨dD, hdD⟩ := ih D0 hD0
      refine ⟨Derivation.res x dC dD hx hnx, ?_⟩
      have hS' : S.sup Finset.card ≤ (insert (resolvent C0 D0 x) S).sup Finset.card :=
        sup_mono (subset_insert _ _)
      simp only [Derivation.width]
      refine max_le (max_le (hdC.trans hS') (hdD.trans hS')) ?_
      exact le_sup (f := Finset.card) (mem_insert_self _ _)
    · obtain ⟨d, hd⟩ := ih C hC
      exact ⟨d, hd.trans (sup_mono (subset_insert _ _))⟩

/-- Every literal of every line is a literal on a variable of `F`. -/
theorem DDer.var_mem {F : CNF} {S : Finset Clause} (h : DDer F S) :
    ∀ C ∈ S, ∀ l ∈ C, l.var ∈ cnfVars F := by
  induction h with
  | empty => intro C hC; simp at hC
  | hyp C0 hS hC0 ih =>
    intro C hC l hl
    rcases mem_insert.1 hC with rfl | hC
    · exact mem_cnfVars.2 ⟨C, hC0, l, hl, rfl⟩
    · exact ih C hC l hl
  | res x C0 D0 hS hC0 hD0 hx hnx ih =>
    intro C hC l hl
    rcases mem_insert.1 hC with rfl | hC
    · rcases mem_union.1 hl with hl | hl
      · exact ih C0 hC0 l (mem_of_mem_erase hl)
      · exact ih D0 hD0 l (mem_of_mem_erase hl)
    · exact ih C hC l hl

theorem DDer.subset_lits {F : CNF} {S : Finset Clause} (h : DDer F S) {C : Clause} (hC : C ∈ S) :
    C ⊆ cnfLits F := by
  intro l hl
  have hv := h.var_mem C hC l hl
  rcases l with ⟨v, p⟩
  cases p <;> exact mem_biUnion.mpr ⟨v, hv, by simp⟩

theorem DDer.card_le_lits {F : CNF} {S : Finset Clause} (h : DDer F S) {C : Clause} (hC : C ∈ S) :
    C.card ≤ (cnfLits F).card := card_le_card (h.subset_lits hC)

theorem DDer.dfat_eq_zero_of_lits_le {F : CNF} {S : Finset Clause} (h : DDer F S) {t : ℕ}
    (ht : (cnfLits F).card ≤ t) : dfat t S = 0 := by
  unfold dfat
  rw [card_eq_zero, filter_eq_empty_iff]
  intro C hC
  exact Nat.not_lt.2 ((h.card_le_lits hC).trans ht)

theorem DDer.width_zero {F : CNF} {S : Finset Clause} (h : DDer F S) {t : ℕ}
    (hz : dfat t S = 0) : S.sup Finset.card ≤ t := by
  unfold dfat at hz
  rw [card_eq_zero, filter_eq_empty_iff] at hz
  exact Finset.sup_le fun C hC => Nat.not_lt.1 (hz hC)

/-! ## Popular literal -/

theorem sum_mem_eq_card {α : Type*} [DecidableEq α] (C L : Finset α) (h : C ⊆ L) :
    (∑ x ∈ L, if x ∈ C then 1 else 0) = C.card := by
  rw [Finset.sum_boole]
  have : L.filter (· ∈ C) = C := by
    ext x; simp only [mem_filter]; exact ⟨fun h => h.2, fun hx => ⟨h hx, hx⟩⟩
  simp [this]

theorem DDer.sum_dfatLit {F : CNF} {S : Finset Clause} (h : DDer F S) (t : ℕ) :
    ∑ l ∈ cnfLits F, dfatLit t l S = ∑ C ∈ S.filter (fun C => t < C.card), C.card := by
  unfold dfatLit
  have : ∀ l, (S.filter fun C => t < C.card ∧ l ∈ C).card =
      ∑ C ∈ S.filter (fun C => t < C.card), if l ∈ C then 1 else 0 := by
    intro l
    rw [Finset.sum_boole, filter_filter]
    simp
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C hC => ?_
  exact sum_mem_eq_card C _ (h.subset_lits (mem_filter.1 hC).1)

theorem DDer.exists_popular_literal {F : CNF} {S : Finset Clause} (h : DDer F S) (t : ℕ)
    (hm : 0 < dfat t S) :
    ∃ l ∈ cnfLits F, t * dfat t S / (cnfLits F).card + 1 ≤ dfatLit t l S := by
  set m := dfat t S with hm_def
  set N := (cnfLits F).card with hN_def
  have hsum := h.sum_dfatLit t
  have hge : (t + 1) * m ≤ ∑ C ∈ S.filter (fun C => t < C.card), C.card := by
    have := Finset.card_nsmul_le_sum (S.filter (fun C => t < C.card)) (fun C => C.card) (t + 1)
      (fun C hC => (mem_filter.1 hC).2)
    simpa [m, dfat, mul_comm] using this
  have hNpos : 0 < N := by
    by_contra hN
    have hempty : cnfLits F = ∅ := card_eq_zero.mp (Nat.eq_zero_of_not_pos hN)
    have hmulpos : 0 < (t + 1) * m := Nat.mul_pos (Nat.succ_pos t) hm
    have hsum0 : ∑ C ∈ S.filter (fun C => t < C.card), C.card = 0 := by
      rw [← hsum]; simp [hempty]
    omega
  have hne : (cnfLits F).Nonempty :=
    nonempty_of_ne_empty (mt card_eq_zero.mpr (ne_of_gt hNpos))
  obtain ⟨l, hl, hsup⟩ :=
    exists_mem_eq_sup (cnfLits F) hne (fun l => dfatLit t l S)
  have hmax : ∑ u ∈ cnfLits F, dfatLit t u S ≤ N * dfatLit t l S := by
    have := sum_le_card_nsmul (cnfLits F) (fun u => dfatLit t u S)
      (dfatLit t l S) (fun u hu => by
        have := le_sup (s := cnfLits F) (f := fun v => dfatLit t v S) hu
        exact hsup ▸ this)
    simpa [nsmul_eq_mul, N] using this
  refine ⟨l, hl, ?_⟩
  by_contra hlt
  have hle : dfatLit t l S ≤ t * m / N := Nat.lt_succ_iff.mp (lt_of_not_ge hlt)
  have hchain1 : ∑ C ∈ S.filter (fun C => t < C.card), C.card ≤ N * (t * m / N) := by
    rw [← hsum]
    exact hmax.trans (Nat.mul_le_mul_left N hle)
  have hchain2 : N * (t * m / N) ≤ t * m := Nat.mul_div_le (t * m) N
  have hgt : t * m < (t + 1) * m := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self t) hm
  omega

/-! ## Restriction of a dag -/

/-- Number of fat lines that survive the restriction `ρ`. -/
noncomputable def dfatAlive (ρ : ℕ → Option Bool) (t : ℕ) (S : Finset Clause) : ℕ :=
  (S.filter fun C => t < C.card ∧ (restrictClause ρ C).isSome).card

theorem dfatAlive_mono (ρ : ℕ → Option Bool) (t : ℕ) {S S' : Finset Clause} (h : S ⊆ S') :
    dfatAlive ρ t S ≤ dfatAlive ρ t S' :=
  card_le_card (filter_subset_filter _ h)

theorem dfatAlive_insert (ρ : ℕ → Option Bool) (t : ℕ) {A : Clause} {S : Finset Clause}
    (hA : A ∉ S) :
    dfatAlive ρ t S + (if t < A.card ∧ (restrictClause ρ A).isSome then 1 else 0) =
      dfatAlive ρ t (insert A S) := by
  unfold dfatAlive
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp [hA])]
  · simp

/-- Restriction of a dag: a dag for the restricted CNF in which every surviving line is subsumed
by a line, and the number of fat lines does not exceed the number of fat surviving lines. -/
theorem DDer.restrict (ρ : ℕ → Option Bool) {F : CNF} {S : Finset Clause} (h : DDer F S) :
    ∃ S' : Finset Clause, DDer (restrictCNF ρ F) S' ∧
      (∀ C ∈ S, ∀ C', restrictClause ρ C = some C' → ∃ D ∈ S', D ⊆ C') ∧
      ∀ t, dfat t S' ≤ dfatAlive ρ t S := by
  induction h with
  | empty => exact ⟨∅, DDer.empty, by simp, fun t => by simp [dfat]⟩
  | hyp C hS hC ih =>
    rename_i S
    obtain ⟨S', hS', hsub, hfat⟩ := ih
    by_cases hCS : C ∈ S
    · rw [insert_eq_of_mem hCS]; exact ⟨S', hS', hsub, hfat⟩
    cases hr : restrictClause ρ C with
    | none =>
      refine ⟨S', hS', ?_, fun t => (hfat t).trans (dfatAlive_mono ρ t (subset_insert _ _))⟩
      intro C1 hC1 C' hC'
      rcases mem_insert.1 hC1 with rfl | hC1
      · rw [hr] at hC'; cases hC'
      · exact hsub C1 hC1 C' hC'
    | some C0 =>
      refine ⟨insert C0 S', DDer.hyp C0 hS' ((mem_restrictCNF_iff ρ F C0).2 ⟨C, hC, hr⟩), ?_, ?_⟩
      · intro C1 hC1 C' hC'
        rcases mem_insert.1 hC1 with rfl | hC1
        · rw [hr] at hC'; cases hC'
          exact ⟨C0, mem_insert_self _ _, Subset.rfl⟩
        · obtain ⟨D, hD, hDs⟩ := hsub C1 hC1 C' hC'
          exact ⟨D, mem_insert_of_mem hD, hDs⟩
      · intro t
        have h1 := dfat_insert_le t C0 S'
        have h2 := dfatAlive_insert ρ t hCS
        have h3 : C0.card ≤ C.card := card_le_card (restrictClause_subset hr)
        have h4 := hfat t
        by_cases ht : t < C0.card
        · have : t < C.card ∧ (restrictClause ρ C).isSome := ⟨by omega, by simp [hr]⟩
          rw [if_pos this] at h2
          rw [if_pos ht] at h1
          omega
        · rw [if_neg ht] at h1
          omega
  | res x C D hS hC hD hx hnx ih =>
    rename_i S
    obtain ⟨S', hS', hsub, hfat⟩ := ih
    by_cases hRS : resolvent C D x ∈ S
    · rw [insert_eq_of_mem hRS]; exact ⟨S', hS', hsub, hfat⟩
    have hmono : ∀ t, dfat t S' ≤ dfatAlive ρ t (insert (resolvent C D x) S) :=
      fun t => (hfat t).trans (dfatAlive_mono ρ t (subset_insert _ _))
    cases hR : restrictClause ρ (resolvent C D x) with
    | none =>
      refine ⟨S', hS', ?_, hmono⟩
      intro C1 hC1 C' hC'
      rcases mem_insert.1 hC1 with rfl | hC1
      · rw [hR] at hC'; cases hC'
      · exact hsub C1 hC1 C' hC'
    | some R' =>
      -- the new surviving line of `S'` (if any) and the subsumption of the resolvent
      have key : ∃ S'' : Finset Clause, DDer (restrictCNF ρ F) S'' ∧ S' ⊆ S'' ∧
          (∃ E ∈ S'', E ⊆ R') ∧
          ∀ t, dfat t S'' ≤ dfat t S' + (if t < R'.card then 1 else 0) := by
        have hRsome : (restrictClause ρ (resolvent C D x)).isSome := by simp [hR]
        cases hCr : restrictClause ρ C with
        | none =>
          cases hDr : restrictClause ρ D with
          | none =>
            rw [restrictClause_resolvent_none_of_parents_none ρ x hCr hDr] at hR; cases hR
          | some D' =>
            obtain ⟨E, hE, hEs⟩ := hsub D hD D' hDr
            have hDR : D' ⊆ R' := restrict_sub_of_left_killed ρ x hx hCr hDr hR
            exact ⟨S', hS', Subset.rfl, ⟨E, hE, hEs.trans hDR⟩, fun t => by omega⟩
        | some Cp =>
          cases hDr : restrictClause ρ D with
          | none =>
            obtain ⟨E, hE, hEs⟩ := hsub C hC Cp hCr
            have hCR : Cp ⊆ R' := restrict_sub_of_right_killed ρ x hnx hCr hDr hR
            exact ⟨S', hS', Subset.rfl, ⟨E, hE, hEs.trans hCR⟩, fun t => by omega⟩
          | some Dp =>
            have hxun : ρ x = none := by
              cases hρ : ρ x with
              | none => rfl
              | some b =>
                cases b
                · have : restrictClause ρ D = none :=
                    (restrictClause_eq_none_iff ρ _).mpr ⟨⟨x, false⟩, hnx, by simp [hρ]⟩
                  rw [this] at hDr; cases hDr
                · have : restrictClause ρ C = none :=
                    (restrictClause_eq_none_iff ρ _).mpr ⟨⟨x, true⟩, hx, by simp [hρ]⟩
                  rw [this] at hCr; cases hCr
            obtain ⟨hReq, _, _⟩ :=
              restrict_resolvent_of_both_some (C := C) (D := D) ρ x hx hnx hCr hDr hxun
            have hR'eq : R' = resolvent Cp Dp x := Option.some.inj (hR.symm.trans hReq)
            obtain ⟨E1, hE1, h1⟩ := hsub C hC Cp hCr
            obtain ⟨E2, hE2, h2⟩ := hsub D hD Dp hDr
            by_cases hE1x : (⟨x, true⟩ : Literal) ∈ E1
            · by_cases hE2x : (⟨x, false⟩ : Literal) ∈ E2
              · refine ⟨insert (resolvent E1 E2 x) S',
                  DDer.res x E1 E2 hS' hE1 hE2 hE1x hE2x, subset_insert _ _,
                  ⟨resolvent E1 E2 x, mem_insert_self _ _, ?_⟩, fun t => ?_⟩
                · rw [hR'eq]; exact resolvent_subset_of_subset h1 h2
                · have := dfat_insert_le t (resolvent E1 E2 x) S'
                  have hc : (resolvent E1 E2 x).card ≤ R'.card := by
                    rw [hR'eq]; exact card_le_card (resolvent_subset_of_subset h1 h2)
                  by_cases ht : t < (resolvent E1 E2 x).card
                  · rw [if_pos ht] at this; rw [if_pos (by omega)]; exact this
                  · rw [if_neg ht] at this; omega
              · refine ⟨S', hS', Subset.rfl, ⟨E2, hE2, ?_⟩, fun t => by omega⟩
                intro l hl
                have hlne : l ≠ ⟨x, false⟩ := fun heq => hE2x (heq ▸ hl)
                rw [hR'eq]
                exact mem_union_right _ (mem_erase.mpr ⟨hlne, h2 hl⟩)
            · refine ⟨S', hS', Subset.rfl, ⟨E1, hE1, ?_⟩, fun t => by omega⟩
              intro l hl
              have hlne : l ≠ ⟨x, true⟩ := fun heq => hE1x (heq ▸ hl)
              rw [hR'eq]
              exact mem_union_left _ (mem_erase.mpr ⟨hlne, h1 hl⟩)
      obtain ⟨S'', hS'', hsubS, ⟨E, hE, hER⟩, hfat''⟩ := key
      refine ⟨S'', hS'', ?_, ?_⟩
      · intro C1 hC1 C' hC'
        rcases mem_insert.1 hC1 with rfl | hC1
        · rw [hR] at hC'; cases hC'; exact ⟨E, hE, hER⟩
        · obtain ⟨D1, hD1, hDs⟩ := hsub C1 hC1 C' hC'
          exact ⟨D1, hsubS hD1, hDs⟩
      · intro t
        have h2 := dfatAlive_insert ρ t hRS
        have h3 : R'.card ≤ (resolvent C D x).card := card_le_card (restrictClause_subset hR)
        have h4 := hfat t
        have h5 := hfat'' t
        by_cases ht : t < R'.card
        · have : t < (resolvent C D x).card ∧ (restrictClause ρ (resolvent C D x)).isSome :=
            ⟨by omega, by simp [hR]⟩
          rw [if_pos this] at h2
          rw [if_pos ht] at h5
          omega
        · rw [if_neg ht] at h5
          omega

theorem DDer.restrict_refutation (ρ : ℕ → Option Bool) {F : CNF} {S : Finset Clause}
    (h : DDer F S) (h0 : (∅ : Clause) ∈ S) :
    ∃ S' : Finset Clause, DDer (restrictCNF ρ F) S' ∧ (∅ : Clause) ∈ S' ∧
      ∀ t, dfat t S' ≤ dfatAlive ρ t S := by
  obtain ⟨S', hS', hsub, hfat⟩ := h.restrict ρ
  obtain ⟨D, hD, hDs⟩ := hsub ∅ h0 ∅ (restrictClause_empty ρ)
  obtain rfl : D = ∅ := Subset.antisymm hDs (empty_subset _)
  exact ⟨S', hS', hD, hfat⟩

theorem dfatAlive_le (ρ : ℕ → Option Bool) (t : ℕ) (S : Finset Clause) :
    dfatAlive ρ t S ≤ dfat t S := by
  refine card_le_card ?_
  intro C hC
  simp only [mem_filter] at hC ⊢
  exact ⟨hC.1, hC.2.1⟩

/-- Restriction killing `l` removes every fat line that contains `l`. -/
theorem DDer.restrict_kill_lit (l : Literal) {F : CNF} {S : Finset Clause} (h : DDer F S)
    (h0 : (∅ : Clause) ∈ S) (t : ℕ) :
    ∃ S' : Finset Clause, DDer (restrictCNF (assignOne l.var l.pos) F) S' ∧ (∅ : Clause) ∈ S' ∧
      dfat t S' ≤ dfat t S - dfatLit t l S := by
  obtain ⟨S', hS', h0', hfat⟩ := h.restrict_refutation (assignOne l.var l.pos) h0
  refine ⟨S', hS', h0', (hfat t).trans ?_⟩
  -- alive fat lines and fat lines containing `l` are disjoint subsets of the fat lines
  have hdisj : Disjoint (S.filter fun C => t < C.card ∧ (restrictClause (assignOne l.var l.pos) C).isSome)
      (S.filter fun C => t < C.card ∧ l ∈ C) := by
    rw [Finset.disjoint_left]
    intro C hC1 hC2
    simp only [mem_filter] at hC1 hC2
    obtain ⟨_, _, hs⟩ := hC1
    have : restrictClause (assignOne l.var l.pos) C = none :=
      (restrictClause_eq_none_iff _ _).2 ⟨l, hC2.2.2, by simp [assignOne]⟩
    simp [this] at hs
  have hsub : (S.filter fun C => t < C.card ∧ (restrictClause (assignOne l.var l.pos) C).isSome) ∪
      (S.filter fun C => t < C.card ∧ l ∈ C) ⊆ S.filter fun C => t < C.card := by
    intro C hC
    simp only [mem_union, mem_filter] at hC ⊢
    rcases hC with ⟨a, b, _⟩ | ⟨a, b, _⟩ <;> exact ⟨a, b⟩
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at this
  unfold dfatAlive dfat dfatLit
  omega

/-! ## Core dag-like BSW induction -/

/-- Dag version of `bsw_width_of_fatCount_aux`: literal budget `N` may over-approximate
`(cnfLits F).card`. -/
theorem bsw_dag_width_aux (N t : ℕ) :
    ∀ (m nv : ℕ) (F : CNF),
      (cnfVars F).card = nv →
      (cnfLits F).card ≤ N →
      ∀ (S : Finset Clause), DDer F S → (∅ : Clause) ∈ S →
        dfat t S = m →
        ∃ d' : Derivation F (∅ : Clause),
          d'.width ≤ cnfWidth F + t + fatSteps N t m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    intro nv
    induction nv using Nat.strong_induction_on with
    | h nv ihnv =>
      intro F hnv hN S hS h0 hfat
      by_cases hmpos : 0 < m
      · have hmF : 0 < dfat t S := by simpa [hfat] using hmpos
        have htF : t < (cnfLits F).card := by
          by_contra hge
          have : dfat t S = 0 := hS.dfat_eq_zero_of_lits_le (Nat.not_lt.mp hge)
          omega
        have htN : t < N := lt_of_lt_of_le htF hN
        have hNF_pos : 0 < (cnfLits F).card := Nat.zero_lt_of_lt htF
        obtain ⟨l, hlits, hpop⟩ := hS.exists_popular_literal t hmF
        obtain ⟨S1, hS1, h01, hfat1⟩ := hS.restrict_kill_lit l h0 t
        have hN1 :
            (cnfLits (restrictCNF (assignOne l.var l.pos) F)).card ≤ N :=
          (cnfLits_card_le_of_vars_subset
            (cnfVars_restrictCNF_subset _ F)).trans hN
        have hm1le : dfat t S1 ≤ fatShrink (cnfLits F).card t m := by
          simp only [fatShrink]
          rw [hfat] at hfat1 hpop
          omega
        have hm1lt : dfat t S1 < m :=
          lt_of_le_of_lt hm1le
            (fatShrink_lt (N := (cnfLits F).card) (t := t) hmpos)
        obtain ⟨d1n, hw1n⟩ :=
          ihm (dfat t S1) hm1lt
            (cnfVars (restrictCNF (assignOne l.var l.pos) F)).card
            (restrictCNF (assignOne l.var l.pos) F) rfl hN1 S1 hS1 h01 rfl
        obtain ⟨U, dU, hUsub, hUwd⟩ := exists_derivation_add_lit d1n
        have hstep :
            fatSteps N t m = 1 + fatSteps N t (fatShrink N t m) :=
          fatSteps_of_pos N t m hmpos
        have hw1n' :
            d1n.width ≤ cnfWidth F + t + fatSteps N t (fatShrink N t m) := by
          have hmono :
              fatSteps N t (dfat t S1) ≤
                fatSteps N t (fatShrink N t m) :=
            fatSteps_mono_m htN
              (hm1le.trans (fatShrink_mono_N hNF_pos hN))
          calc
            d1n.width
                ≤ cnfWidth (restrictCNF (assignOne l.var l.pos) F) + t +
                    fatSteps N t (dfat t S1) := hw1n
            _ ≤ cnfWidth F + t + fatSteps N t (dfat t S1) :=
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
          obtain ⟨S0, hS0, h00, hfat0⟩ :=
            hS.restrict_refutation (assignOne l.var (!l.pos)) h0
          have hN0 :
              (cnfLits (restrictCNF (assignOne l.var (!l.pos)) F)).card ≤ N :=
            (cnfLits_card_le_of_vars_subset
              (cnfVars_restrictCNF_subset _ F)).trans hN
          have hm0le : dfat t S0 ≤ m := by
            have := hfat0 t
            have := dfatAlive_le (assignOne l.var (!l.pos)) t S
            omega
          have hvar : l.var ∈ cnfVars F := mem_cnfVars_of_mem_cnfLits hlits
          have hnv0lt :
              (cnfVars (restrictCNF (assignOne l.var (!l.pos)) F)).card < nv := by
            have hss :=
              cnfVars_restrictCNF_ssubset_assignOne (F := F) (!l.pos) hvar
            simpa [hnv] using card_lt_card hss
          have hAll :
              ∀ C ∈ restrictCNF (assignOne l.var (!l.pos)) F,
                ∃ e : Derivation F C,
                  e.width ≤ max (cnfWidth F) dU.width :=
            fun C hC =>
              exists_derivation_false_branch_clause l dU hUsing hC
          by_cases hm0lt : dfat t S0 < m
          · obtain ⟨d0n, hw0n⟩ :=
              ihm (dfat t S0) hm0lt
                (cnfVars (restrictCNF (assignOne l.var (!l.pos)) F)).card
                (restrictCNF (assignOne l.var (!l.pos)) F) rfl hN0 S0 hS0 h00 rfl
            have hw0bound :
                d0n.width ≤ cnfWidth F + t + fatSteps N t m := by
              calc
                d0n.width
                    ≤ cnfWidth (restrictCNF (assignOne l.var (!l.pos)) F) +
                        t + fatSteps N t (dfat t S0) := hw0n
                _ ≤ cnfWidth F + t + fatSteps N t (dfat t S0) :=
                  Nat.add_le_add_right
                    (Nat.add_le_add_right (cnfWidth_restrictCNF_le _ F) t) _
                _ ≤ cnfWidth F + t + fatSteps N t m :=
                  Nat.add_le_add_left (fatSteps_mono_m htN hm0le) _
            obtain ⟨dG, hwG⟩ :=
              exists_derivation_graft_width
                (max (cnfWidth F) dU.width) hAll d0n
            exact ⟨dG,
              hwG.trans (max_le (max_le (by omega) hUbound) hw0bound)⟩
          · have hm0eq : dfat t S0 = m :=
              le_antisymm hm0le (Nat.not_lt.mp hm0lt)
            obtain ⟨d0n, hw⟩ :=
              ihnv (cnfVars (restrictCNF (assignOne l.var (!l.pos)) F)).card
                hnv0lt (restrictCNF (assignOne l.var (!l.pos)) F) rfl hN0 S0 hS0 h00
                hm0eq
            have hw0n :
                d0n.width ≤
                  cnfWidth (restrictCNF (assignOne l.var (!l.pos)) F) + t +
                    fatSteps N t (dfat t S0) := by
              simpa [hm0eq] using hw
            have hw0bound :
                d0n.width ≤ cnfWidth F + t + fatSteps N t m := by
              calc
                d0n.width
                    ≤ cnfWidth (restrictCNF (assignOne l.var (!l.pos)) F) +
                        t + fatSteps N t (dfat t S0) := hw0n
                _ ≤ cnfWidth F + t + fatSteps N t (dfat t S0) :=
                  Nat.add_le_add_right
                    (Nat.add_le_add_right (cnfWidth_restrictCNF_le _ F) t) _
                _ ≤ cnfWidth F + t + fatSteps N t m :=
                  Nat.add_le_add_left (fatSteps_mono_m htN hm0le) _
            obtain ⟨dG, hwG⟩ :=
              exists_derivation_graft_width
                (max (cnfWidth F) dU.width) hAll d0n
            exact ⟨dG,
              hwG.trans (max_le (max_le (by omega) hUbound) hw0bound)⟩
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmpos
        subst hm0
        obtain ⟨d, hd⟩ := hS.to_tree ∅ h0
        have hz := hS.width_zero hfat
        refine ⟨d, ?_⟩
        simp only [fatSteps_zero, Nat.add_zero]
        omega

/-- **Ben-Sasson and Wigderson, dag-like**: a dag refutation with `m` fat lines (more than `t`
literals) yields a tree refutation of width at most `cnfWidth F + t + fatSteps (2 n) t m`. -/
theorem bsw_dag_width_of_fatCount (F : CNF) (t : ℕ) {S : Finset Clause} (hS : DDer F S)
    (h0 : (∅ : Clause) ∈ S) :
    ∃ d' : Derivation F (∅ : Clause),
      d'.width ≤
        cnfWidth F + t + fatSteps (2 * (cnfVars F).card) t (dfat t S) := by
  have hN : (cnfLits F).card ≤ 2 * (cnfVars F).card := by
    simp [cnfLits_card]
  exact bsw_dag_width_aux (2 * (cnfVars F).card) t (dfat t S) (cnfVars F).card F rfl hN S hS h0 rfl
/-! ## Rate corollary -/

theorem bsw_dag_width_log_bound (F : CNF) (W : ℕ)
    (hW : ∀ d : Derivation F (∅ : Clause), W ≤ d.width)
    {S : Finset Clause} (hS : DDer F S) (h0 : (∅ : Clause) ∈ S)
    (t : ℕ) (ht : 0 < t)
    (htN : t ≤ 2 * (cnfVars F).card) :
    W ≤ cnfWidth F + t +
      fatBlock (2 * (cnfVars F).card) t * (Nat.log 2 S.card + 1) := by
  set N := 2 * (cnfVars F).card
  obtain ⟨d', hw⟩ := bsw_dag_width_of_fatCount F t hS h0
  have hWd' := hW d'
  have h1 : W ≤ cnfWidth F + t + fatSteps N t (dfat t S) := by
    simpa [N] using hWd'.trans hw
  have hlog := fatSteps_le_log (N := N) (t := t) (m := dfat t S) ht htN
  have hlogS :
      fatSteps N t (dfat t S) ≤
        fatBlock N t * (Nat.log 2 S.card + 1) :=
    hlog.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_mono_right (dfat_le_card t S))))
  exact h1.trans (Nat.add_le_add_left hlogS _)

/-- Rate corollary: width lower bound implies exponential size at `bswRateConst = 24`. -/
theorem bsw_dag_size_lower_bound (F : CNF) (W : ℕ)
    (hW : ∀ d : Derivation F (∅ : Clause), W ≤ d.width)
    {T : Finset Clause} (hS : DDer F T) (h0 : (∅ : Clause) ∈ T) :
    2 ^ ((W - cnfWidth F) * (W - cnfWidth F) /
          (bswRateConst * (cnfVars F).card)) ≤ T.card := by
  set n := (cnfVars F).card
  set N := 2 * n
  set Δ := W - cnfWidth F
  set S := T.card
  set L := Nat.log 2 S + 1
  set e := Δ * Δ / (bswRateConst * n)
  have hSpos : 0 < S := card_pos.2 ⟨∅, h0⟩
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
  have hW_le_N : W ≤ N := by
    obtain ⟨d, hd⟩ := hS.to_tree ∅ h0
    have : T.sup Finset.card ≤ (cnfLits F).card :=
      Finset.sup_le fun C hC => hS.card_le_lits hC
    have h2 : W ≤ (cnfLits F).card := (hW d).trans (hd.trans this)
    simpa [N, n, cnfLits_card] using h2
  have hΔN : Δ ≤ N := (Nat.sub_le W (cnfWidth F)).trans hW_le_N
  have htN : Δ / 2 ≤ N := (Nat.div_le_self Δ 2).trans hΔN
  have hlog :=
    bsw_dag_width_log_bound F W hW hS h0 (Δ / 2) ht (by simpa [N] using htN)
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


end SATurday.ProofComplexity
