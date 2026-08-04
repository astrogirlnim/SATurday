import Theory.ProofComplexity.MatchingRestriction

/-!
# The Semantic Monotone Calculus and the Positive Simulation (R1, BP96 / G8)

BP96 run the large clause kill argument inside a positive calculus whose lines
are monotone clauses judged only by which critical permutations falsify them.
This module defines that calculus and certifies the simulation:

1. `MonoDeriv n C`: a derivation of the positive grid clause `C`. An axiom is
   any line whose falsifying set is contained in a pigeon axiom's falsifying
   set. An inference is any line whose falsifying set is covered by the union
   of two premises' falsifying sets. Both are sound for critical semantics.
2. Simulation: a resolution derivation of `C` from `phpCNF n` yields a
   `MonoDeriv n (monotoneClause n hn C)` of no larger size. Hole axioms map to
   axiom lines because no critical permutation falsifies a hole clause;
   resolution steps map to `sem` steps via `Fals_resolvent_subset`.
3. A resolution refutation therefore yields a monotone refutation
   (`MonoDeriv n ∅`) of no larger size.

The kill counting (restriction of monotone lines and the width contradiction)
is deferred to the next formalize cycles.

LOG: R1 monotone semantic calculus module (BP96 / G8a)
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Falsifying set helpers -/

/-- The monotone transform preserves the falsifying set. -/
theorem Fals_monotoneClause {n : ℕ} (hn : 0 < n) (C : Clause) :
    Fals n (monotoneClause n hn C) = Fals n C := by
  ext pi
  simp [Fals, falsifies_monotoneClause_iff hn]

/-- Hole clauses are never falsified by critical permutations. -/
theorem Fals_holeClause_empty {n : ℕ} {C : Clause} (hC : C ∈ holeClauses n) :
    Fals n C = ∅ :=
  card_eq_zero.mp (complexity_holeClause hC)

/-- Semantic coverage transfers the left out pigeon sets. -/
theorem L_subset_of_Fals_subset_union {n : ℕ} {C A B : Clause}
    (hw : Fals n C ⊆ Fals n A ∪ Fals n B) : L n C ⊆ L n A ∪ L n B := by
  intro i hi
  obtain ⟨pi, hlast, hf⟩ := (mem_L_iff C i).mp hi
  have hmem : pi ∈ Fals n C := mem_filter.mpr ⟨mem_univ pi, hf⟩
  rcases mem_union.mp (hw hmem) with h | h
  · exact mem_union_left _ ((mem_L_iff A i).mpr ⟨pi, hlast, (mem_filter.mp h).2⟩)
  · exact mem_union_right _ ((mem_L_iff B i).mpr ⟨pi, hlast, (mem_filter.mp h).2⟩)

/-- Semantic domination transfers the left out pigeon set. -/
theorem L_subset_of_Fals_subset {n : ℕ} {C A : Clause}
    (hw : Fals n C ⊆ Fals n A) : L n C ⊆ L n A := by
  intro i hi
  obtain ⟨pi, hlast, hf⟩ := (mem_L_iff C i).mp hi
  have hmem : pi ∈ Fals n C := mem_filter.mpr ⟨mem_univ pi, hf⟩
  exact (mem_L_iff A i).mpr ⟨pi, hlast, (mem_filter.mp (hw hmem)).2⟩

/-! ## Grid support of derivation clauses -/

/-- Every literal of a PHP clause is a grid literal. -/
theorem phpCNF_lit_grid {n : ℕ} {C : Clause} (hC : C ∈ phpCNF n) {l : Literal}
    (hl : l ∈ C) : isGridVar n l.var := by
  rcases mem_union.mp hC with hp | hh
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := mem_image.mp hl
    exact isGridVar_pvar n i j
  · simp only [holeClauses, mem_biUnion, mem_image, mem_filter, mem_univ,
      true_and] at hh
    obtain ⟨j, i, i', hlt, rfl⟩ := hh
    rcases mem_insert.mp hl with rfl | hl2
    · exact isGridVar_pvar n i j
    · rw [mem_singleton] at hl2
      rw [hl2]
      exact isGridVar_pvar n i' j

/-- Every literal in a clause derived from PHP is a grid literal. -/
theorem derivation_lit_grid {n : ℕ} {C : Clause} (d : Derivation (phpCNF n) C)
    {l : Literal} (hl : l ∈ C) : isGridVar n l.var := by
  have hv : l.var ∈ cnfVars (phpCNF n) :=
    derivation_clauseVars_subset d (mem_image_of_mem _ hl)
  obtain ⟨C0, hC0, l0, hl0, hveq⟩ := mem_cnfVars.mp hv
  rw [← hveq]
  exact phpCNF_lit_grid hC0 hl0

/-- Monotone transforms of grid supported clauses are positive grid clauses. -/
theorem monotoneClause_subset_gridPosLits {n : ℕ} (hn : 0 < n) {C : Clause}
    (hC : ∀ l ∈ C, isGridVar n l.var) :
    monotoneClause n hn C ⊆ gridPosLits n := by
  intro l' hl'
  simp only [monotoneClause, mem_biUnion] at hl'
  obtain ⟨l, hl, hl'mem⟩ := hl'
  have hgrid := hC l hl
  simp only [monotoneLiteral] at hl'mem
  by_cases hp : l.pos = true
  · -- Positive literals survive unchanged and decode as grid positions.
    simp only [hp, ↓reduceIte, mem_singleton] at hl'mem
    rw [hl'mem]
    refine (mem_gridPosLits_iff).mpr
      ⟨gridPigeon n hn l.var hgrid, gridHole n hn l.var hgrid, ?_⟩
    have hv := pvar_grid_eq n hn l.var hgrid
    calc l = ⟨l.var, l.pos⟩ := rfl
      _ = ⟨pvar n (gridPigeon n hn l.var hgrid) (gridHole n hn l.var hgrid), true⟩ := by
          rw [hv, hp]
  · -- Negative grid literals expand into positive grid literals.
    have hpf : l.pos = false := eq_false_of_ne_true hp
    simp only [hpf, Bool.false_eq_true, ↓reduceIte, hgrid, ↓reduceDIte,
      mem_image] at hl'mem
    obtain ⟨t, _, rfl⟩ := hl'mem
    exact (mem_gridPosLits_iff).mpr ⟨t, _, rfl⟩

/-- The monotone transform of the empty clause is empty. -/
theorem monotoneClause_empty {n : ℕ} (hn : 0 < n) :
    monotoneClause n hn (∅ : Clause) = ∅ := by
  simp [monotoneClause]

/-! ## The semantic monotone calculus -/

/-- BP96 positive calculus over critical semantics. An `ax` line is dominated
by a pigeon axiom; a `sem` line is covered by two premises. -/
inductive MonoDeriv (n : ℕ) : Clause → Type where
  | ax (i : Fin (n + 1)) (C : Clause) (hC : C ⊆ gridPosLits n)
      (hw : Fals n C ⊆ Fals n (pigeonClause n i)) : MonoDeriv n C
  | sem (A B : Clause) (C : Clause) (hC : C ⊆ gridPosLits n)
      (hw : Fals n C ⊆ Fals n A ∪ Fals n B)
      (dA : MonoDeriv n A) (dB : MonoDeriv n B) : MonoDeriv n C

/-- Size of a monotone derivation: number of lines counted with multiplicity. -/
def MonoDeriv.size {n : ℕ} : {C : Clause} → MonoDeriv n C → ℕ
  | _, .ax _ _ _ _ => 1
  | _, .sem _ _ _ _ _ dA dB => dA.size + dB.size + 1

/-- Every line of a monotone derivation is a positive grid clause. -/
theorem MonoDeriv.concl_subset {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    C ⊆ gridPosLits n := by
  cases md with
  | ax _ _ hC _ => exact hC
  | sem _ _ _ hC _ _ _ => exact hC

/-! ## Simulation from resolution -/

/-- BP96 positive simulation: resolution derivations from PHP map to monotone
derivations of the transformed conclusion without size increase. -/
theorem exists_monoDeriv_of_derivation {n : ℕ} (hn : 0 < n) {C : Clause}
    (d : Derivation (phpCNF n) C) :
    ∃ md : MonoDeriv n (monotoneClause n hn C), md.size ≤ d.size := by
  induction d with
  | hyp C hC =>
      have hgridsub : monotoneClause n hn C ⊆ gridPosLits n :=
        monotoneClause_subset_gridPosLits hn fun l hl => phpCNF_lit_grid hC hl
      rcases mem_union.mp hC with hp | hh
      · -- Pigeon axioms map to themselves semantically.
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        refine ⟨.ax i _ hgridsub ?_, ?_⟩
        · rw [Fals_monotoneClause hn]
        · simp [MonoDeriv.size, Derivation.size]
      · -- Hole axioms have empty falsifying sets.
        refine ⟨.ax ⟨0, Nat.succ_pos n⟩ _ hgridsub ?_, ?_⟩
        · rw [Fals_monotoneClause hn, Fals_holeClause_empty hh]
          exact empty_subset _
        · simp [MonoDeriv.size, Derivation.size]
  | @res x Cp Dp dC dD hx hnx ihC ihD =>
      obtain ⟨mC, hsC⟩ := ihC
      obtain ⟨mD, hsD⟩ := ihD
      have hgridsub : monotoneClause n hn (resolvent Cp Dp x) ⊆ gridPosLits n := by
        refine monotoneClause_subset_gridPosLits hn fun l hl => ?_
        exact derivation_lit_grid (Derivation.res x dC dD hx hnx) hl
      refine ⟨.sem _ _ _ hgridsub ?_ mC mD, ?_⟩
      · -- Coverage: monotone falsifying sets match the resolution ones.
        rw [Fals_monotoneClause hn, Fals_monotoneClause hn, Fals_monotoneClause hn]
        exact Fals_resolvent_subset Cp Dp x
      · show mC.size + mD.size + 1 ≤ dC.size + dD.size + 1
        omega

/-- Transport a monotone derivation across a conclusion equality. -/
theorem exists_monoDeriv_of_concl_eq {n : ℕ} {C C' : Clause} (h : C = C')
    (md : MonoDeriv n C) : ∃ md' : MonoDeriv n C', md'.size = md.size := by
  subst h
  exact ⟨md, rfl⟩

/-- A resolution refutation of PHP yields a monotone refutation of no larger
size. -/
theorem exists_monoDeriv_refutation {n : ℕ} (hn : 0 < n)
    (d : Derivation (phpCNF n) (∅ : Clause)) :
    ∃ md : MonoDeriv n (∅ : Clause), md.size ≤ d.size := by
  obtain ⟨md, hs⟩ := exists_monoDeriv_of_derivation hn d
  obtain ⟨md', hs'⟩ := exists_monoDeriv_of_concl_eq (monotoneClause_empty hn) md
  exact ⟨md', by omega⟩

/-! ## G8b: lines of a monotone derivation and the width lemma -/

/-- All conclusions appearing in a monotone derivation. -/
def MonoDeriv.lines {n : ℕ} : {C : Clause} → MonoDeriv n C → Finset Clause
  | C, .ax _ _ _ _ => {C}
  | C, .sem _ _ _ _ _ dA dB => insert C (dA.lines ∪ dB.lines)

theorem MonoDeriv.concl_mem_lines {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    C ∈ md.lines := by
  cases md with
  | ax _ _ _ _ => simp [MonoDeriv.lines]
  | sem _ _ _ _ _ dA dB => simp [MonoDeriv.lines]

/-- Line count is bounded by derivation size. -/
theorem MonoDeriv.lines_card_le_size {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    md.lines.card ≤ md.size := by
  induction md with
  | ax _ _ _ _ => simp [MonoDeriv.lines, MonoDeriv.size]
  | sem A B C hC hw dA dB ihA ihB =>
      simp only [MonoDeriv.lines, MonoDeriv.size]
      have h1 := card_insert_le C (dA.lines ∪ dB.lines)
      have h2 := card_union_le dA.lines dB.lines
      omega

/-- Every line of a monotone derivation is a positive grid clause. -/
theorem MonoDeriv.mem_lines_subset_grid {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    ∀ C' ∈ md.lines, C' ⊆ gridPosLits n := by
  induction md with
  | ax i C hC hw =>
      intro C' hC'
      simp only [MonoDeriv.lines, mem_singleton] at hC'
      rw [hC']
      exact hC
  | sem A B C hC hw dA dB ihA ihB =>
      intro C' hC'
      simp only [MonoDeriv.lines, mem_insert, mem_union] at hC'
      rcases hC' with rfl | h | h
      · exact hC
      · exact ihA C' h
      · exact ihB C' h

/-- BP96 width walk in the monotone calculus: a conclusion of high
pigeonComplexity forces a line in the intermediate band. -/
theorem MonoDeriv.exists_intermediate_line {n : ℕ} (hn : 1 ≤ n) :
    ∀ {C : Clause} (md : MonoDeriv n C),
      2 * (n + 1) / 3 < pigeonComplexity n C →
      ∃ C' ∈ md.lines, (n + 1) / 3 < pigeonComplexity n C' ∧
        pigeonComplexity n C' ≤ 2 * (n + 1) / 3 := by
  intro C md
  induction md with
  | ax i C hC hw =>
      intro hhigh
      -- Axiom lines are dominated by a pigeon axiom, whose complexity is 1.
      have hsub := L_subset_of_Fals_subset hw
      have hone : (L n (pigeonClause n i)).card = 1 := by
        simpa [pigeonComplexity] using pigeonComplexity_pigeonClause n i
      have hle : pigeonComplexity n C ≤ 1 := by
        have hcard := card_le_card hsub
        rw [hone] at hcard
        exact hcard
      simp only [pigeonComplexity] at hle hhigh
      omega
  | sem A B C hC hw dA dB ihA ihB =>
      intro hhigh
      -- Semantic coverage gives subadditivity of pigeonComplexity.
      have hle : pigeonComplexity n C ≤
          pigeonComplexity n A + pigeonComplexity n B := by
        have hsub := L_subset_of_Fals_subset_union hw
        calc (L n C).card
            ≤ (L n A ∪ L n B).card := card_le_card hsub
          _ ≤ (L n A).card + (L n B).card := card_union_le _ _
      by_cases hAh : 2 * (n + 1) / 3 < pigeonComplexity n A
      · obtain ⟨C', hmem, h1, h2⟩ := ihA hAh
        refine ⟨C', ?_, h1, h2⟩
        simp only [MonoDeriv.lines]
        exact mem_insert_of_mem (mem_union_left _ hmem)
      · by_cases hBh : 2 * (n + 1) / 3 < pigeonComplexity n B
        · obtain ⟨C', hmem, h1, h2⟩ := ihB hBh
          refine ⟨C', ?_, h1, h2⟩
          simp only [MonoDeriv.lines]
          exact mem_insert_of_mem (mem_union_right _ hmem)
        · by_cases hAmid : (n + 1) / 3 < pigeonComplexity n A
          · refine ⟨A, ?_, hAmid, Nat.not_lt.mp hAh⟩
            simp only [MonoDeriv.lines]
            exact mem_insert_of_mem (mem_union_left _ dA.concl_mem_lines)
          · by_cases hBmid : (n + 1) / 3 < pigeonComplexity n B
            · refine ⟨B, ?_, hBmid, Nat.not_lt.mp hBh⟩
              simp only [MonoDeriv.lines]
              exact mem_insert_of_mem (mem_union_right _ dB.concl_mem_lines)
            · have h1 : pigeonComplexity n A ≤ (n + 1) / 3 := Nat.not_lt.mp hAmid
              have h2 : pigeonComplexity n B ≤ (n + 1) / 3 := Nat.not_lt.mp hBmid
              omega

theorem pos_of_mem_gridPosLits {n : ℕ} {l : Literal} (hl : l ∈ gridPosLits n) :
    l.pos = true := by
  obtain ⟨i, j, rfl⟩ := (mem_gridPosLits_iff).mp hl
  rfl

/-- The monotone transform fixes positive clauses. -/
theorem monotoneClause_of_pos {n : ℕ} (hn : 0 < n) {C : Clause}
    (hC : ∀ l ∈ C, l.pos = true) : monotoneClause n hn C = C := by
  ext l'
  simp only [monotoneClause, mem_biUnion]
  constructor
  · rintro ⟨l, hl, hl'⟩
    simp only [monotoneLiteral, hC l hl, ↓reduceIte, mem_singleton] at hl'
    rw [hl']
    exact hl
  · intro hl'
    exact ⟨l', hl', by simp [monotoneLiteral, hC l' hl']⟩

/-- Width lemma: every monotone refutation of PHP(n+1, n) with n ≥ 1 contains
a line of width at least `largeThreshold n`. -/
theorem MonoDeriv.exists_wide_line {n : ℕ} (hn : 1 ≤ n)
    (md : MonoDeriv n (∅ : Clause)) :
    ∃ C' ∈ md.lines, largeThreshold n ≤ C'.card := by
  have hhigh : 2 * (n + 1) / 3 < pigeonComplexity n (∅ : Clause) := by
    rw [pigeonComplexity_empty]
    omega
  obtain ⟨C', hmem, hlo, hhi⟩ := md.exists_intermediate_line hn hhigh
  refine ⟨C', hmem, ?_⟩
  have hpos : ∀ l ∈ C', l.pos = true := fun l hl =>
    pos_of_mem_gridPosLits (md.mem_lines_subset_grid C' hmem hl)
  have hn0 : 0 < n := hn
  have hcard := monotoneClause_card_ge_largeThreshold hn0 C' hlo hhi
  rwa [monotoneClause_of_pos hn0 hpos] at hcard

/-! ## G8c: matching restriction of monotone lines

Placing pigeon `i` in hole `j` corresponds semantically to extending a
critical permutation of PHP(k+1, k) to one of PHP(k+2, k+1) that places `i` in
`j`. The extension `critExtend` is built from `finSuccEquiv'` on the pigeon
side and on the slot side. The line restriction `monoRestrict` drops the row
and column literals and renames survivors onto the small grid; falsification
transports exactly along `critExtend` for unkilled lines.
-/

private theorem bool_eq_of_true_iff {a b : Bool} (h : (a = true) ↔ (b = true)) :
    a = b := by
  cases a <;> cases b <;> simp_all

/-- Slot embedding sends the left out marker to the left out marker. -/
theorem castSucc_succAbove_last {k : ℕ} (j : Fin (k + 1)) :
    (Fin.castSucc j).succAbove (Fin.last k) = Fin.last (k + 1) := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by
    simp [Fin.le_castSucc_iff, Fin.castSucc_lt_last])]
  simp [Fin.succ_last]

/-- Slot embedding commutes with hole embedding. -/
theorem castSucc_succAbove_castSucc {k : ℕ} (j : Fin (k + 1)) (t : Fin k) :
    (Fin.castSucc j).succAbove (Fin.castSucc t) = Fin.castSucc (j.succAbove t) := by
  rcases lt_or_ge (Fin.castSucc t) j with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa using h),
      Fin.succAbove_of_castSucc_lt _ _ h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa using h),
      Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_castSucc]

/-- Extend a PHP(k+1, k) critical permutation to PHP(k+2, k+1) by placing
pigeon `i` in hole `j` and reindexing everything else. -/
def critExtend (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (pi' : Crit k) : Crit (k + 1) :=
  (finSuccEquiv' i).trans (pi'.optionCongr.trans (finSuccEquiv' (Fin.castSucc j)).symm)

theorem critExtend_apply_placed {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (pi' : Crit k) : critExtend k i j pi' i = Fin.castSucc j := by
  simp [critExtend]

theorem critExtend_apply_succAbove {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (pi' : Crit k) (i' : Fin (k + 1)) :
    critExtend k i j pi' (i.succAbove i') = (Fin.castSucc j).succAbove (pi' i') := by
  simp [critExtend]

/-- The extended permutation never leaves out a reindexed pigeon unless the
small permutation does. -/
theorem critExtend_last_iff {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (pi' : Crit k) (i' : Fin (k + 1)) :
    critExtend k i j pi' (i.succAbove i') = Fin.last (k + 1) ↔
      pi' i' = Fin.last k := by
  rw [critExtend_apply_succAbove]
  constructor
  · intro h
    rcases Fin.eq_castSucc_or_eq_last (pi' i') with ⟨t, ht⟩ | ht
    · rw [ht, castSucc_succAbove_castSucc] at h
      exact absurd h (Fin.castSucc_lt_last _).ne
    · exact ht
  · intro h
    rw [h, castSucc_succAbove_last]

/-- The extension places pigeon `i` in hole `j`. -/
theorem critExtend_assign_place {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (pi' : Crit k) :
    criticalAssignment (k + 1) (critExtend k i j pi') (pvar (k + 1) i j) = true :=
  (criticalAssignment_pvar _ i j).mpr (critExtend_apply_placed i j pi')

/-- On embedded grid variables the extension agrees with the small critical
assignment. -/
theorem critExtend_assign_embed {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (pi' : Crit k) (i' : Fin (k + 1)) (j' : Fin k) :
    criticalAssignment (k + 1) (critExtend k i j pi')
        (matchingEmbedVar k i j i' j') =
      criticalAssignment k pi' (pvar k i' j') := by
  refine bool_eq_of_true_iff ?_
  rw [show matchingEmbedVar k i j i' j' =
      pvar (k + 1) (i.succAbove i') (j.succAbove j') from rfl,
    criticalAssignment_pvar, criticalAssignment_pvar, critExtend_apply_succAbove,
    ← castSucc_succAbove_castSucc, Fin.succAbove_right_inj]

/-- Matching restriction of a monotone line: drop forced literals and rename
survivors onto the smaller grid. -/
noncomputable def monoRestrict (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (C : Clause) : Clause :=
  renameClause (matchingUnrenameσ k i j)
    (C.filter fun l => matchingLookup (k + 1) i j l.var = none)

theorem monoRestrict_empty (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) :
    monoRestrict k i j (∅ : Clause) = ∅ := by
  simp [monoRestrict, renameClause]

/-- Restriction never increases the width of a line. -/
theorem monoRestrict_card_le (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (C : Clause) : (monoRestrict k i j C).card ≤ C.card :=
  le_trans (card_image_le) (card_filter_le _ _)

/-- Unforced grid variables sit strictly off the matched row and column. -/
theorem offgrid_of_matchingLookup_none {k : ℕ} {i : Fin (k + 2)}
    {j : Fin (k + 1)} {a : Fin (k + 2)} {b : Fin (k + 1)}
    (h : matchingLookup (k + 1) i j (pvar (k + 1) a b) = none) :
    a ≠ i ∧ b ≠ j := by
  constructor
  · rintro rfl
    by_cases hb : b = j
    · rw [hb, matchingLookup_place] at h
      exact Option.some_ne_none _ h
    · rw [matchingLookup_row a hb] at h
      exact Option.some_ne_none _ h
  · rintro rfl
    by_cases ha : a = i
    · rw [ha, matchingLookup_place] at h
      exact Option.some_ne_none _ h
    · rw [matchingLookup_col b ha] at h
      exact Option.some_ne_none _ h

/-- Restricted lines are positive grid clauses of the smaller PHP. -/
theorem monoRestrict_subset_grid {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    {C : Clause} (hC : C ⊆ gridPosLits (k + 1)) :
    monoRestrict k i j C ⊆ gridPosLits k := by
  intro l' hl'
  obtain ⟨l, hlf, rfl⟩ := (mem_renameClause_iff _ _ _).mp hl'
  obtain ⟨hlC, hnone⟩ := mem_filter.mp hlf
  obtain ⟨a, b, rfl⟩ := (mem_gridPosLits_iff).mp (hC hlC)
  obtain ⟨ha, hb⟩ := offgrid_of_matchingLookup_none hnone
  obtain ⟨i'', rfl⟩ := Fin.exists_succAbove_eq ha
  obtain ⟨b'', rfl⟩ := Fin.exists_succAbove_eq hb
  refine (mem_gridPosLits_iff).mpr ⟨i'', b'', ?_⟩
  show (⟨matchingUnrenameσ k i j (matchingEmbedVar k i j i'' b''), true⟩ : Literal) = _
  rw [matchingUnrenameσ_embed]

/-- Killed lines are satisfied by every extended critical assignment. -/
theorem clauseSat_critExtend_of_killed {k : ℕ} {i : Fin (k + 2)}
    {j : Fin (k + 1)} {C : Clause}
    (hkill : (⟨pvar (k + 1) i j, true⟩ : Literal) ∈ C) (pi' : Crit k) :
    clauseSat (criticalAssignment (k + 1) (critExtend k i j pi')) C :=
  ⟨⟨pvar (k + 1) i j, true⟩, hkill, critExtend_assign_place i j pi'⟩

/-- Falsification correspondence: for an unkilled positive grid line, the
restricted line is falsified by `pi'` exactly when the original line is
falsified by the extension of `pi'`. -/
theorem falsifies_monoRestrict_iff {k : ℕ} {i : Fin (k + 2)} {j : Fin (k + 1)}
    {C : Clause} (hC : C ⊆ gridPosLits (k + 1))
    (hkill : (⟨pvar (k + 1) i j, true⟩ : Literal) ∉ C) (pi' : Crit k) :
    falsifies k (monoRestrict k i j C) pi' ↔
      falsifies (k + 1) C (critExtend k i j pi') := by
  unfold falsifies
  rw [not_iff_not]
  constructor
  · -- A satisfied restricted literal pulls back to a satisfied original one.
    rintro ⟨l', hl', hsat'⟩
    obtain ⟨l, hlf, rfl⟩ := (mem_renameClause_iff _ _ _).mp hl'
    obtain ⟨hlC, hnone⟩ := mem_filter.mp hlf
    obtain ⟨a, b, rfl⟩ := (mem_gridPosLits_iff).mp (hC hlC)
    obtain ⟨ha, hb⟩ := offgrid_of_matchingLookup_none hnone
    obtain ⟨i'', rfl⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨b'', rfl⟩ := Fin.exists_succAbove_eq hb
    refine ⟨_, hlC, ?_⟩
    show criticalAssignment (k + 1) (critExtend k i j pi')
      (pvar (k + 1) (i.succAbove i'') (j.succAbove b'')) = true
    rw [show pvar (k + 1) (i.succAbove i'') (j.succAbove b'') =
        matchingEmbedVar k i j i'' b'' from rfl, critExtend_assign_embed]
    have hlit : renameLit (matchingUnrenameσ k i j)
        (⟨pvar (k + 1) (i.succAbove i'') (j.succAbove b''), true⟩ : Literal) =
        (⟨pvar k i'' b'', true⟩ : Literal) := by
      show (⟨matchingUnrenameσ k i j (matchingEmbedVar k i j i'' b''), true⟩ :
        Literal) = _
      rw [matchingUnrenameσ_embed]
    rw [hlit] at hsat'
    exact hsat'
  · -- A satisfied original literal survives restriction and stays satisfied.
    rintro ⟨l, hlC, hsat⟩
    obtain ⟨a, b, rfl⟩ := (mem_gridPosLits_iff).mp (hC hlC)
    have hab : critExtend k i j pi' a = Fin.castSucc b :=
      (criticalAssignment_pvar _ a b).mp hsat
    by_cases hai : a = i
    · -- The satisfied literal would be the placed one, which is excluded.
      subst hai
      rw [critExtend_apply_placed] at hab
      have hbj : b = j := (Fin.castSucc_injective _ hab.symm)
      rw [hbj] at hlC
      exact absurd hlC hkill
    · obtain ⟨i'', rfl⟩ := Fin.exists_succAbove_eq hai
      rw [critExtend_apply_succAbove] at hab
      rcases Fin.eq_castSucc_or_eq_last (pi' i'') with ⟨b'', hb''⟩ | hlast
      · rw [hb'', castSucc_succAbove_castSucc] at hab
        have hbeq : j.succAbove b'' = b := Fin.castSucc_injective _ hab
        refine ⟨renameLit (matchingUnrenameσ k i j)
          (⟨pvar (k + 1) (i.succAbove i'') b, true⟩ : Literal), ?_, ?_⟩
        · refine (mem_renameClause_iff _ _ _).mpr
            ⟨_, mem_filter.mpr ⟨hlC, ?_⟩, rfl⟩
          rw [← hbeq]
          exact matchingLookup_off_grid_succAbove i j i'' b''
        · have hlit : renameLit (matchingUnrenameσ k i j)
              (⟨pvar (k + 1) (i.succAbove i'') b, true⟩ : Literal) =
              (⟨pvar k i'' b'', true⟩ : Literal) := by
            rw [← hbeq]
            show (⟨matchingUnrenameσ k i j (matchingEmbedVar k i j i'' b''), true⟩ :
              Literal) = _
            rw [matchingUnrenameσ_embed]
          rw [hlit]
          show criticalAssignment k pi' (pvar k i'' b'') = true
          exact (criticalAssignment_pvar _ i'' b'').mpr hb''
      · rw [hlast, castSucc_succAbove_last] at hab
        exact absurd hab.symm (Fin.castSucc_lt_last b).ne

/-- Fals form of the correspondence, forward direction. -/
theorem critExtend_mem_Fals_of_monoRestrict {k : ℕ} {i : Fin (k + 2)}
    {j : Fin (k + 1)} {C : Clause} (hC : C ⊆ gridPosLits (k + 1))
    (hkill : (⟨pvar (k + 1) i j, true⟩ : Literal) ∉ C) {pi' : Crit k}
    (h : pi' ∈ Fals k (monoRestrict k i j C)) :
    critExtend k i j pi' ∈ Fals (k + 1) C := by
  rw [Fals, mem_filter] at h ⊢
  exact ⟨mem_univ _, (falsifies_monoRestrict_iff hC hkill pi').mp h.2⟩

/-- Fals form of the correspondence, backward direction. -/
theorem monoRestrict_mem_Fals_of_critExtend {k : ℕ} {i : Fin (k + 2)}
    {j : Fin (k + 1)} {C : Clause} (hC : C ⊆ gridPosLits (k + 1))
    (hkill : (⟨pvar (k + 1) i j, true⟩ : Literal) ∉ C) {pi' : Crit k}
    (h : critExtend k i j pi' ∈ Fals (k + 1) C) :
    pi' ∈ Fals k (monoRestrict k i j C) := by
  rw [Fals, mem_filter] at h ⊢
  exact ⟨mem_univ _, (falsifies_monoRestrict_iff hC hkill pi').mpr h.2⟩

/-- Killed lines never appear in the falsifying set of an extension. -/
theorem critExtend_notMem_Fals_of_killed {k : ℕ} {i : Fin (k + 2)}
    {j : Fin (k + 1)} {C : Clause}
    (hkill : (⟨pvar (k + 1) i j, true⟩ : Literal) ∈ C) (pi' : Crit k) :
    critExtend k i j pi' ∉ Fals (k + 1) C := by
  rw [Fals, mem_filter]
  rintro ⟨-, hf⟩
  exact hf (clauseSat_critExtend_of_killed hkill pi')

/-- The placed pigeon's axiom is never falsified by an extension. -/
theorem critExtend_notMem_Fals_pigeonClause_placed {k : ℕ} (i : Fin (k + 2))
    (j : Fin (k + 1)) (pi' : Crit k) :
    critExtend k i j pi' ∉ Fals (k + 1) (pigeonClause (k + 1) i) :=
  critExtend_notMem_Fals_of_killed (mem_pigeonClause i j) pi'

/-- Reindexed pigeon axioms transport falsification along the extension. -/
theorem critExtend_falsifies_pigeonClause_iff {k : ℕ} (i : Fin (k + 2))
    (j : Fin (k + 1)) (pi' : Crit k) (i'' : Fin (k + 1)) :
    falsifies (k + 1) (pigeonClause (k + 1) (i.succAbove i''))
        (critExtend k i j pi') ↔
      falsifies k (pigeonClause k i'') pi' := by
  rw [falsifies_pigeonClause_iff, falsifies_pigeonClause_iff]
  exact critExtend_last_iff i j pi' i''

end SATurday.ProofComplexity
