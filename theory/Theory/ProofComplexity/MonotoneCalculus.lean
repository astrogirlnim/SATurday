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
by a pigeon axiom; a `sem` line is covered by two premises; a `wk` line is
covered by one premise (needed when a premise is killed by a restriction). -/
inductive MonoDeriv (n : ℕ) : Clause → Type where
  | ax (i : Fin (n + 1)) (C : Clause) (hC : C ⊆ gridPosLits n)
      (hw : Fals n C ⊆ Fals n (pigeonClause n i)) : MonoDeriv n C
  | sem (A B : Clause) (C : Clause) (hC : C ⊆ gridPosLits n)
      (hw : Fals n C ⊆ Fals n A ∪ Fals n B)
      (dA : MonoDeriv n A) (dB : MonoDeriv n B) : MonoDeriv n C
  | wk (A : Clause) (C : Clause) (hC : C ⊆ gridPosLits n)
      (hw : Fals n C ⊆ Fals n A) (dA : MonoDeriv n A) : MonoDeriv n C

/-- Size of a monotone derivation: number of lines counted with multiplicity. -/
def MonoDeriv.size {n : ℕ} : {C : Clause} → MonoDeriv n C → ℕ
  | _, .ax _ _ _ _ => 1
  | _, .sem _ _ _ _ _ dA dB => dA.size + dB.size + 1
  | _, .wk _ _ _ _ dA => dA.size + 1

/-- Every line of a monotone derivation is a positive grid clause. -/
theorem MonoDeriv.concl_subset {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    C ⊆ gridPosLits n := by
  cases md with
  | ax _ _ hC _ => exact hC
  | sem _ _ _ hC _ _ _ => exact hC
  | wk _ _ hC _ _ => exact hC

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

/-! ## G8b: lines of a monotone derivation and the width lemma -/

/-- All conclusions appearing in a monotone derivation. -/
def MonoDeriv.lines {n : ℕ} : {C : Clause} → MonoDeriv n C → Finset Clause
  | C, .ax _ _ _ _ => {C}
  | C, .sem _ _ _ _ _ dA dB => insert C (dA.lines ∪ dB.lines)
  | C, .wk _ _ _ _ dA => insert C dA.lines

theorem MonoDeriv.concl_mem_lines {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    C ∈ md.lines := by
  cases md with
  | ax _ _ _ _ => simp [MonoDeriv.lines]
  | sem _ _ _ _ _ dA dB => simp [MonoDeriv.lines]
  | wk _ _ _ _ dA => simp [MonoDeriv.lines]

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
  | wk A C hC hw dA ihA =>
      simp only [MonoDeriv.lines, MonoDeriv.size]
      have h1 := card_insert_le C dA.lines
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
  | wk A C hC hw dA ihA =>
      intro C' hC'
      simp only [MonoDeriv.lines, mem_insert] at hC'
      rcases hC' with rfl | h
      · exact hC
      · exact ihA C' h

/-- Transport a monotone derivation across a conclusion equality, preserving
size and lines. -/
theorem exists_monoDeriv_of_concl_eq {n : ℕ} {C C' : Clause} (h : C = C')
    (md : MonoDeriv n C) :
    ∃ md' : MonoDeriv n C', md'.size = md.size ∧ md'.lines = md.lines := by
  subst h
  exact ⟨md, rfl, rfl⟩

/-- A resolution refutation of PHP yields a monotone refutation of no larger
size. -/
theorem exists_monoDeriv_refutation {n : ℕ} (hn : 0 < n)
    (d : Derivation (phpCNF n) (∅ : Clause)) :
    ∃ md : MonoDeriv n (∅ : Clause), md.size ≤ d.size := by
  obtain ⟨md, hs⟩ := exists_monoDeriv_of_derivation hn d
  obtain ⟨md', hs', -⟩ := exists_monoDeriv_of_concl_eq (monotoneClause_empty hn) md
  exact ⟨md', by omega⟩

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
  | wk A C hC hw dA ihA =>
      intro hhigh
      -- Coverage by one premise: complexity can only go up toward the premise.
      have hle : pigeonComplexity n C ≤ pigeonComplexity n A :=
        card_le_card (L_subset_of_Fals_subset hw)
      obtain ⟨C', hmem, h1, h2⟩ := ihA (by omega)
      refine ⟨C', ?_, h1, h2⟩
      simp only [MonoDeriv.lines]
      exact mem_insert_of_mem hmem

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

/-! ## G8d: restriction of monotone derivations -/

/-- The kill predicate for a matching step on monotone lines. -/
def monoKilled (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) (C : Clause) : Prop :=
  (⟨pvar (k + 1) i j, true⟩ : Literal) ∈ C

instance monoKilled_decidable {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1))
    (C : Clause) : Decidable (monoKilled k i j C) :=
  inferInstanceAs (Decidable (_ ∈ _))

private theorem image_filter_lines_mono {k : ℕ} {i : Fin (k + 2)}
    {j : Fin (k + 1)} {s t : Finset Clause} (h : s ⊆ t) :
    (s.filter fun D => ¬ monoKilled k i j D).image (monoRestrict k i j) ⊆
      (t.filter fun D => ¬ monoKilled k i j D).image (monoRestrict k i j) :=
  image_subset_image (filter_subset_filter _ h)

/-- BP96 restriction step at the derivation level: an unkilled conclusion of a
monotone derivation over PHP(k+2, k+1) restricts to a monotone derivation over
PHP(k+1, k) of no larger size, whose lines are restrictions of unkilled lines
of the original. -/
theorem exists_monoDeriv_restrict {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1)) :
    ∀ {C : Clause} (md : MonoDeriv (k + 1) C),
      ¬ monoKilled k i j C →
      ∃ md' : MonoDeriv k (monoRestrict k i j C),
        md'.size ≤ md.size ∧
        md'.lines ⊆
          (md.lines.filter fun D => ¬ monoKilled k i j D).image
            (monoRestrict k i j) := by
  intro C md
  induction md with
  | ax i0 C hC hw =>
      intro hkill
      have hC' : monoRestrict k i j C ⊆ gridPosLits k :=
        monoRestrict_subset_grid i j hC
      by_cases hplace : i0 = i
      · -- Dominated by the placed pigeon's axiom: falsifying set collapses.
        refine ⟨.ax 0 _ hC' ?_, ?_, ?_⟩
        · intro pi' hpi'
          have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
          rw [hplace] at hw
          exact ((critExtend_notMem_Fals_pigeonClause_placed i j pi')
            (hw hmem)).elim
        · simp [MonoDeriv.size]
        · intro C' hC'mem
          simp only [MonoDeriv.lines, mem_singleton] at hC'mem
          rw [hC'mem]
          refine mem_image_of_mem _ (mem_filter.mpr ⟨?_, hkill⟩)
          simp [MonoDeriv.lines]
      · -- Dominated by a surviving pigeon's axiom: transport the domination.
        obtain ⟨i0', rfl⟩ := Fin.exists_succAbove_eq hplace
        refine ⟨.ax i0' _ hC' ?_, ?_, ?_⟩
        · intro pi' hpi'
          have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
          have hfals := (mem_filter.mp (hw hmem)).2
          have hfals' := (critExtend_falsifies_pigeonClause_iff i j pi' i0').mp hfals
          exact mem_filter.mpr ⟨mem_univ _, hfals'⟩
        · simp [MonoDeriv.size]
        · intro C' hC'mem
          simp only [MonoDeriv.lines, mem_singleton] at hC'mem
          rw [hC'mem]
          refine mem_image_of_mem _ (mem_filter.mpr ⟨?_, hkill⟩)
          simp [MonoDeriv.lines]
  | sem A B C hC hw dA dB ihA ihB =>
      intro hkill
      have hC' : monoRestrict k i j C ⊆ gridPosLits k :=
        monoRestrict_subset_grid i j hC
      have hAgrid := dA.concl_subset
      have hBgrid := dB.concl_subset
      have hconclmem : monoRestrict k i j C ∈
          ((MonoDeriv.sem A B C hC hw dA dB).lines.filter
            fun D => ¬ monoKilled k i j D).image (monoRestrict k i j) := by
        refine mem_image_of_mem _ (mem_filter.mpr ⟨?_, hkill⟩)
        simp [MonoDeriv.lines]
      have hsubA : dA.lines ⊆ (MonoDeriv.sem A B C hC hw dA dB).lines := by
        intro D hD
        simp only [MonoDeriv.lines]
        exact mem_insert_of_mem (mem_union_left _ hD)
      have hsubB : dB.lines ⊆ (MonoDeriv.sem A B C hC hw dA dB).lines := by
        intro D hD
        simp only [MonoDeriv.lines]
        exact mem_insert_of_mem (mem_union_right _ hD)
      by_cases hkA : monoKilled k i j A
      · by_cases hkB : monoKilled k i j B
        · -- Both premises killed: the conclusion's falsifying set collapses.
          refine ⟨.ax 0 _ hC' ?_, ?_, ?_⟩
          · intro pi' hpi'
            have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
            rcases mem_union.mp (hw hmem) with h | h
            · exact ((critExtend_notMem_Fals_of_killed hkA pi') h).elim
            · exact ((critExtend_notMem_Fals_of_killed hkB pi') h).elim
          · simp only [MonoDeriv.size]
            omega
          · intro C' hC'mem
            simp only [MonoDeriv.lines, mem_singleton] at hC'mem
            rw [hC'mem]
            exact hconclmem
        · -- Left premise killed: weaken from the surviving right premise.
          obtain ⟨mB, hsB, hlB⟩ := ihB hkB
          refine ⟨.wk _ _ hC' ?_ mB, ?_, ?_⟩
          · intro pi' hpi'
            have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
            rcases mem_union.mp (hw hmem) with h | h
            · exact ((critExtend_notMem_Fals_of_killed hkA pi') h).elim
            · exact monoRestrict_mem_Fals_of_critExtend hBgrid hkB h
          · simp only [MonoDeriv.size]
            omega
          · intro C' hC'mem
            simp only [MonoDeriv.lines, mem_insert] at hC'mem
            rcases hC'mem with rfl | h
            · exact hconclmem
            · exact image_filter_lines_mono hsubB (hlB h)
      · by_cases hkB : monoKilled k i j B
        · -- Right premise killed: weaken from the surviving left premise.
          obtain ⟨mA, hsA, hlA⟩ := ihA hkA
          refine ⟨.wk _ _ hC' ?_ mA, ?_, ?_⟩
          · intro pi' hpi'
            have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
            rcases mem_union.mp (hw hmem) with h | h
            · exact monoRestrict_mem_Fals_of_critExtend hAgrid hkA h
            · exact ((critExtend_notMem_Fals_of_killed hkB pi') h).elim
          · simp only [MonoDeriv.size]
            omega
          · intro C' hC'mem
            simp only [MonoDeriv.lines, mem_insert] at hC'mem
            rcases hC'mem with rfl | h
            · exact hconclmem
            · exact image_filter_lines_mono hsubA (hlA h)
        · -- Both premises survive: transport the two premise coverage.
          obtain ⟨mA, hsA, hlA⟩ := ihA hkA
          obtain ⟨mB, hsB, hlB⟩ := ihB hkB
          refine ⟨.sem _ _ _ hC' ?_ mA mB, ?_, ?_⟩
          · intro pi' hpi'
            have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
            rcases mem_union.mp (hw hmem) with h | h
            · exact mem_union_left _
                (monoRestrict_mem_Fals_of_critExtend hAgrid hkA h)
            · exact mem_union_right _
                (monoRestrict_mem_Fals_of_critExtend hBgrid hkB h)
          · simp only [MonoDeriv.size]
            omega
          · intro C' hC'mem
            simp only [MonoDeriv.lines, mem_insert, mem_union] at hC'mem
            rcases hC'mem with rfl | h | h
            · exact hconclmem
            · exact image_filter_lines_mono hsubA (hlA h)
            · exact image_filter_lines_mono hsubB (hlB h)
  | wk A C hC hw dA ihA =>
      intro hkill
      have hC' : monoRestrict k i j C ⊆ gridPosLits k :=
        monoRestrict_subset_grid i j hC
      have hAgrid := dA.concl_subset
      have hconclmem : monoRestrict k i j C ∈
          ((MonoDeriv.wk A C hC hw dA).lines.filter
            fun D => ¬ monoKilled k i j D).image (monoRestrict k i j) := by
        refine mem_image_of_mem _ (mem_filter.mpr ⟨?_, hkill⟩)
        simp [MonoDeriv.lines]
      have hsubA : dA.lines ⊆ (MonoDeriv.wk A C hC hw dA).lines := by
        intro D hD
        simp only [MonoDeriv.lines]
        exact mem_insert_of_mem hD
      by_cases hkA : monoKilled k i j A
      · -- The only premise is killed: the falsifying set collapses.
        refine ⟨.ax 0 _ hC' ?_, ?_, ?_⟩
        · intro pi' hpi'
          have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
          exact ((critExtend_notMem_Fals_of_killed hkA pi') (hw hmem)).elim
        · simp only [MonoDeriv.size]
          omega
        · intro C' hC'mem
          simp only [MonoDeriv.lines, mem_singleton] at hC'mem
          rw [hC'mem]
          exact hconclmem
      · -- The premise survives: weaken from its restriction.
        obtain ⟨mA, hsA, hlA⟩ := ihA hkA
        refine ⟨.wk _ _ hC' ?_ mA, ?_, ?_⟩
        · intro pi' hpi'
          have hmem := critExtend_mem_Fals_of_monoRestrict hC hkill hpi'
          exact monoRestrict_mem_Fals_of_critExtend hAgrid hkA (hw hmem)
        · simp only [MonoDeriv.size]
          omega
        · intro C' hC'mem
          simp only [MonoDeriv.lines, mem_insert] at hC'mem
          rcases hC'mem with rfl | h
          · exact hconclmem
          · exact image_filter_lines_mono hsubA (hlA h)

/-- Restriction of a monotone refutation is a monotone refutation of the
smaller PHP with no larger size, and its lines restrict unkilled lines. -/
theorem exists_monoDeriv_refutation_restrict {k : ℕ} (i : Fin (k + 2))
    (j : Fin (k + 1)) (md : MonoDeriv (k + 1) (∅ : Clause)) :
    ∃ md' : MonoDeriv k (∅ : Clause),
      md'.size ≤ md.size ∧
      md'.lines ⊆
        (md.lines.filter fun D => ¬ monoKilled k i j D).image
          (monoRestrict k i j) := by
  have hkill : ¬ monoKilled k i j (∅ : Clause) := by
    simp [monoKilled]
  obtain ⟨md', hs, hl⟩ := exists_monoDeriv_restrict i j md hkill
  obtain ⟨md'', hs'', hl''⟩ :=
    exists_monoDeriv_of_concl_eq (monoRestrict_empty k i j) md'
  refine ⟨md'', by omega, ?_⟩
  rw [hl'']
  exact hl

/-! ## G8e: threshold generic averaging and the kill step

The accepted averaging lemmas fix the threshold at `largeThreshold n`. The
iteration needs a fixed final threshold `W` across shrinking scales, so we
recertify the double counting with `W` as a parameter and package one full
kill step at the derivation level.
-/

/-- Threshold generic double counting: some grid literal hits an average
share of any family of `W` wide positive grid clauses. -/
theorem exists_popular_grid_literal_W {n : ℕ} (hn : 0 < n) (W : ℕ)
    (Large : Finset Clause)
    (hwide : ∀ C ∈ Large, W ≤ C.card)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      Large.card * W ≤
        (n + 1) * n * (Large.filter (killedByMatching n i j)).card := by
  classical
  by_cases hL : Large = ∅
  · refine ⟨⟨0, by omega⟩, ⟨0, hn⟩, ?_⟩
    simp [hL]
  have hsum_ge : Large.card * W ≤ ∑ C ∈ Large, C.card := by
    have := card_nsmul_le_sum (s := Large) (f := fun C => C.card)
      (n := W) (fun C hC => hwide C hC)
    simpa [nsmul_eq_mul] using this
  have hsum_eq := sum_card_eq_sum_hitCount n Large hsub
  have hV : (gridPosLits n).card = (n + 1) * n := gridPosLits_card n
  have hne : (gridPosLits n).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    simp [hempty] at hV
    omega
  obtain ⟨l, hl, hsup⟩ :=
    exists_mem_eq_sup (gridPosLits n) hne (fun l => hitCount Large l)
  have hmax : ∑ t ∈ gridPosLits n, hitCount Large t ≤
      (gridPosLits n).card * hitCount Large l := by
    have := sum_le_card_nsmul (gridPosLits n) (fun t => hitCount Large t)
      (hitCount Large l)
      (fun t ht => hsup ▸ le_sup (f := fun u => hitCount Large u) ht)
    simpa [nsmul_eq_mul] using this
  have hbound : Large.card * W ≤ (n + 1) * n * hitCount Large l := by
    calc Large.card * W
        ≤ ∑ C ∈ Large, C.card := hsum_ge
      _ = ∑ t ∈ gridPosLits n, hitCount Large t := hsum_eq
      _ ≤ (gridPosLits n).card * hitCount Large l := hmax
      _ = (n + 1) * n * hitCount Large l := by rw [hV]
  obtain ⟨i, j, rfl⟩ := (mem_gridPosLits_iff).mp hl
  refine ⟨i, j, ?_⟩
  simpa [hitCount, killedByMatching] using hbound

/-- Threshold generic survivor bound: some matching leaves at most
`L - L * W / V` of the wide clauses unkilled, and strictly fewer when the
family is nonempty and the threshold positive. -/
theorem wide_survivors_le_W {n : ℕ} (hn : 0 < n) (W : ℕ)
    (Large : Finset Clause)
    (hwide : ∀ C ∈ Large, W ≤ C.card)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      (Large.filter fun C => ¬ killedByMatching n i j C).card ≤
        Large.card - Large.card * W / ((n + 1) * n) ∧
      (0 < Large.card → 0 < W →
        (Large.filter fun C => ¬ killedByMatching n i j C).card < Large.card) := by
  obtain ⟨i, j, hpop⟩ := exists_popular_grid_literal_W hn W Large hwide hsub
  refine ⟨i, j, ?_, ?_⟩
  · have hdiv : Large.card * W / ((n + 1) * n) ≤
        (Large.filter (killedByMatching n i j)).card :=
      Nat.div_le_of_le_mul hpop
    rw [filter_not_killed_card]
    exact Nat.sub_le_sub_left hdiv _
  · intro hL hW
    have hkillpos : 0 < (Large.filter (killedByMatching n i j)).card := by
      by_contra h0
      have : (Large.filter (killedByMatching n i j)).card = 0 := by omega
      rw [this, Nat.mul_zero] at hpop
      have : Large.card * W = 0 := Nat.le_zero.mp hpop
      have := Nat.mul_pos hL hW
      omega
    rw [filter_not_killed_card]
    exact Nat.sub_lt hL hkillpos

/-- One full BP96 kill step at the derivation level: restrict along a popular
matching, shrinking the scale by one, never growing the size, and cutting the
`W` wide line count by its average share. -/
theorem exists_monoDeriv_kill_step {k : ℕ} (W : ℕ) (hW : 0 < W)
    (md : MonoDeriv (k + 1) (∅ : Clause)) :
    ∃ md' : MonoDeriv k (∅ : Clause),
      md'.size ≤ md.size ∧
      (md'.lines.filter fun C => W ≤ C.card).card ≤
        (md.lines.filter fun C => W ≤ C.card).card -
          (md.lines.filter fun C => W ≤ C.card).card * W /
            ((k + 2) * (k + 1)) ∧
      (0 < (md.lines.filter fun C => W ≤ C.card).card →
        (md'.lines.filter fun C => W ≤ C.card).card <
          (md.lines.filter fun C => W ≤ C.card).card) := by
  classical
  set Wide := md.lines.filter fun C => W ≤ C.card with hWide
  have hwide : ∀ C ∈ Wide, W ≤ C.card := fun C hC => (mem_filter.mp hC).2
  have hsub : ∀ C ∈ Wide, C ⊆ gridPosLits (k + 1) := fun C hC =>
    md.mem_lines_subset_grid C (mem_filter.mp hC).1
  obtain ⟨i, j, hle, hlt⟩ :=
    wide_survivors_le_W (Nat.succ_pos k) W Wide hwide hsub
  obtain ⟨md', hs, hl⟩ := exists_monoDeriv_refutation_restrict i j md
  refine ⟨md', hs, ?_, ?_⟩
  · -- Wide restricted lines come from unkilled wide originals.
    have hincl : md'.lines.filter (fun C => W ≤ C.card) ⊆
        (Wide.filter fun C => ¬ killedByMatching (k + 1) i j C).image
          (monoRestrict k i j) := by
      intro C' hC'
      obtain ⟨hC'mem, hC'wide⟩ := mem_filter.mp hC'
      obtain ⟨D, hD, rfl⟩ := mem_image.mp (hl hC'mem)
      obtain ⟨hDmem, hDunkilled⟩ := mem_filter.mp hD
      have hDwide : W ≤ D.card :=
        le_trans hC'wide (monoRestrict_card_le k i j D)
      refine mem_image_of_mem _ (mem_filter.mpr ⟨?_, hDunkilled⟩)
      exact mem_filter.mpr ⟨hDmem, hDwide⟩
    calc (md'.lines.filter fun C => W ≤ C.card).card
        ≤ ((Wide.filter fun C => ¬ killedByMatching (k + 1) i j C).image
            (monoRestrict k i j)).card := card_le_card hincl
      _ ≤ (Wide.filter fun C => ¬ killedByMatching (k + 1) i j C).card :=
          card_image_le
      _ ≤ Wide.card - Wide.card * W / ((k + 2) * (k + 1)) := hle
  · intro hpos
    have hincl : md'.lines.filter (fun C => W ≤ C.card) ⊆
        (Wide.filter fun C => ¬ killedByMatching (k + 1) i j C).image
          (monoRestrict k i j) := by
      intro C' hC'
      obtain ⟨hC'mem, hC'wide⟩ := mem_filter.mp hC'
      obtain ⟨D, hD, rfl⟩ := mem_image.mp (hl hC'mem)
      obtain ⟨hDmem, hDunkilled⟩ := mem_filter.mp hD
      have hDwide : W ≤ D.card :=
        le_trans hC'wide (monoRestrict_card_le k i j D)
      refine mem_image_of_mem _ (mem_filter.mpr ⟨?_, hDunkilled⟩)
      exact mem_filter.mpr ⟨hDmem, hDwide⟩
    calc (md'.lines.filter fun C => W ≤ C.card).card
        ≤ ((Wide.filter fun C => ¬ killedByMatching (k + 1) i j C).image
            (monoRestrict k i j)).card := card_le_card hincl
      _ ≤ (Wide.filter fun C => ¬ killedByMatching (k + 1) i j C).card :=
          card_image_le
      _ < Wide.card := hlt hpos hW

/-- Halved rate multiplicative form of one kill step: while the wide family is
dense (`V ≤ L * W`), the survivor count decays geometrically with denominator
`2 * V`. -/
theorem kill_step_mul {V W L L' : ℕ} (hV : 0 < V)
    (hdense : V ≤ L * W) (h : L' ≤ L - L * W / V) :
    2 * V * L' ≤ (2 * V - W) * L := by
  set q := L * W / V with hqdef
  have hdm : V * q + L * W % V = L * W := Nat.div_add_mod (L * W) V
  have hmod : L * W % V < V := Nat.mod_lt _ hV
  have hq1 : 1 ≤ q := (Nat.one_le_div_iff hV).mpr hdense
  have hVq : V ≤ V * q := by
    calc V = V * 1 := (Nat.mul_one V).symm
      _ ≤ V * q := Nat.mul_le_mul_left V hq1
  -- Floor recovery: since V ≤ L * W, twice the floored product dominates it.
  have hrecover : L * W ≤ 2 * V * q := by
    calc L * W = V * q + L * W % V := hdm.symm
      _ ≤ V * q + V := Nat.add_le_add_left (le_of_lt hmod) _
      _ ≤ V * q + V * q := Nat.add_le_add_left hVq _
      _ = 2 * V * q := by ring
  -- Multiply the survivor bound by 2V and cancel the floor.
  have hstep : 2 * V * L' ≤ 2 * V * (L - q) := Nat.mul_le_mul_left (2 * V) h
  have hexp : 2 * V * (L - q) = 2 * V * L - 2 * V * q := by
    rw [Nat.mul_comm (2 * V) (L - q), Nat.sub_mul, Nat.mul_comm L (2 * V),
      Nat.mul_comm q (2 * V)]
  have hfinal : 2 * V * L - 2 * V * q ≤ 2 * V * L - L * W :=
    Nat.sub_le_sub_left hrecover _
  have hgoal_exp : (2 * V - W) * L = 2 * V * L - W * L := Nat.sub_mul _ _ _
  rw [hgoal_exp, Nat.mul_comm W L]
  calc 2 * V * L' ≤ 2 * V * (L - q) := hstep
    _ = 2 * V * L - 2 * V * q := hexp
    _ ≤ 2 * V * L - L * W := hfinal

/-! ## G8f: iterating the kill step

The dense phase decays the wide count geometrically (multiplicative invariant
with a stuck term `V₀`); the sparse tail kills at least one wide line per
step. Composing wipes out every `W` wide line while shrinking PHP by
`t + s` pigeons.
-/

/-- Transport a monotone refutation across a scale equality. -/
theorem exists_monoDeriv_of_scale_eq {n n' : ℕ} (h : n = n')
    (md : MonoDeriv n (∅ : Clause)) :
    ∃ md' : MonoDeriv n' (∅ : Clause),
      md'.size = md.size ∧ md'.lines = md.lines := by
  subst h
  exact ⟨md, rfl, rfl⟩

/-- Number of `W` wide lines of a monotone derivation. -/
noncomputable def wideCount (W : ℕ) {n : ℕ} {C : Clause} (md : MonoDeriv n C) : ℕ :=
  (md.lines.filter fun D => W ≤ D.card).card

/-- Dense phase invariant: after `t` kill steps the wide count decays
geometrically up to a stuck term of size `V₀`. -/
theorem exists_monoDeriv_iter {W V₀ : ℕ} (hW : 0 < W) (hV₀ : 0 < V₀) :
    ∀ (t n : ℕ), t ≤ n →
      (∀ k, k < n → (k + 2) * (k + 1) ≤ V₀) →
      ∀ (md : MonoDeriv n (∅ : Clause)),
        ∃ md' : MonoDeriv (n - t) (∅ : Clause),
          md'.size ≤ md.size ∧
          (2 * V₀) ^ t * (wideCount W md' * W) ≤
            (2 * V₀ - W) ^ t * (wideCount W md * W) + (2 * V₀) ^ t * V₀ := by
  intro t
  induction t with
  | zero =>
      intro n _ _ md
      refine ⟨md, le_rfl, ?_⟩
      simp only [pow_zero, Nat.one_mul]
      omega
  | succ t ih =>
      intro n ht huni md
      -- Run t steps first, landing at scale n - t ≥ 1.
      obtain ⟨md1, hs1, hinv⟩ := ih n (by omega) huni md
      have hpos : 1 ≤ n - t := by omega
      obtain ⟨k, hk⟩ : ∃ k, n - t = k + 1 := ⟨n - t - 1, by omega⟩
      obtain ⟨md2, hs2, hl2⟩ := exists_monoDeriv_of_scale_eq hk md1
      -- One more kill step at scale k + 1.
      obtain ⟨md3, hs3, hcut, _⟩ := exists_monoDeriv_kill_step W hW md2
      -- Return to the n - (t+1) indexing.
      have hk' : k = n - (t + 1) := by omega
      obtain ⟨md4, hs4, hl4⟩ := exists_monoDeriv_of_scale_eq hk' md3
      refine ⟨md4, by omega, ?_⟩
      -- Uniformize the volume at the current scale.
      set L := wideCount W md1 with hL
      set L' := wideCount W md4 with hL'
      have hLmd2 : wideCount W md2 = L := by
        simp only [wideCount, hl2, hL]
      have hL'md3 : wideCount W md3 = L' := by
        simp only [wideCount, hL', hl4]
      have hVscale : (k + 2) * (k + 1) ≤ V₀ := huni k (by omega)
      have hVscale_pos : 0 < (k + 2) * (k + 1) := by positivity
      have hdivmono : L * W / V₀ ≤ L * W / ((k + 2) * (k + 1)) :=
        Nat.div_le_div_left hVscale hVscale_pos
      have hstep : L' ≤ L - L * W / V₀ := by
        have e2 : (md2.lines.filter fun C => W ≤ C.card).card = L := hLmd2
        have e3 : (md3.lines.filter fun C => W ≤ C.card).card = L' := hL'md3
        calc L' = (md3.lines.filter fun C => W ≤ C.card).card := e3.symm
          _ ≤ (md2.lines.filter fun C => W ≤ C.card).card -
              (md2.lines.filter fun C => W ≤ C.card).card * W /
                ((k + 2) * (k + 1)) := hcut
          _ = L - L * W / ((k + 2) * (k + 1)) := by rw [e2]
          _ ≤ L - L * W / V₀ := Nat.sub_le_sub_left hdivmono L
      by_cases hdense : V₀ ≤ L * W
      · -- Dense: multiplicative decay via the halved rate step.
        have hmul : 2 * V₀ * L' ≤ (2 * V₀ - W) * L :=
          kill_step_mul hV₀ hdense hstep
        calc (2 * V₀) ^ (t + 1) * (L' * W)
            = (2 * V₀) ^ t * ((2 * V₀ * L') * W) := by ring
          _ ≤ (2 * V₀) ^ t * (((2 * V₀ - W) * L) * W) := by
              refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmul)
          _ = (2 * V₀ - W) * ((2 * V₀) ^ t * (L * W)) := by ring
          _ ≤ (2 * V₀ - W) *
              ((2 * V₀ - W) ^ t * (wideCount W md * W) + (2 * V₀) ^ t * V₀) :=
              Nat.mul_le_mul_left _ hinv
          _ = (2 * V₀ - W) ^ (t + 1) * (wideCount W md * W) +
              (2 * V₀ - W) * ((2 * V₀) ^ t * V₀) := by ring
          _ ≤ (2 * V₀ - W) ^ (t + 1) * (wideCount W md * W) +
              (2 * V₀) ^ (t + 1) * V₀ := by
              refine Nat.add_le_add_left ?_ _
              calc (2 * V₀ - W) * ((2 * V₀) ^ t * V₀)
                  ≤ 2 * V₀ * ((2 * V₀) ^ t * V₀) :=
                    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                _ = (2 * V₀) ^ (t + 1) * V₀ := by ring
      · -- Sparse: the wide count is already below the stuck term.
        have hsparse : L * W < V₀ := Nat.not_le.mp hdense
        have hL'le : L' * W ≤ V₀ := by
          have h1 : L' ≤ L := le_trans hstep (Nat.sub_le _ _)
          have h2 : L' * W ≤ L * W := Nat.mul_le_mul_right _ h1
          exact le_of_lt (lt_of_le_of_lt h2 hsparse)
        calc (2 * V₀) ^ (t + 1) * (L' * W)
            ≤ (2 * V₀) ^ (t + 1) * V₀ := Nat.mul_le_mul_left _ hL'le
          _ ≤ (2 * V₀ - W) ^ (t + 1) * (wideCount W md * W) +
              (2 * V₀) ^ (t + 1) * V₀ := Nat.le_add_left _ _

/-- Sparse tail: with at most `s` wide lines left, `s` further kill steps
remove them all. -/
theorem exists_monoDeriv_tail {W : ℕ} (hW : 0 < W) :
    ∀ (s n : ℕ), s ≤ n →
      ∀ (md : MonoDeriv n (∅ : Clause)), wideCount W md ≤ s →
        ∃ md' : MonoDeriv (n - s) (∅ : Clause),
          md'.size ≤ md.size ∧ wideCount W md' = 0 := by
  intro s
  induction s with
  | zero =>
      intro n _ md hcount
      exact ⟨md, le_rfl, by omega⟩
  | succ s ih =>
      intro n hs md hcount
      have hpos : 1 ≤ n := by omega
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨md1, hs1, hl1⟩ := exists_monoDeriv_of_scale_eq hk md
      obtain ⟨md2, hs2, hcut, hstrict⟩ := exists_monoDeriv_kill_step W hW md1
      have hcount1 : wideCount W md1 = wideCount W md := by
        simp only [wideCount, hl1]
      have e1 : wideCount W md1 = (md1.lines.filter fun C => W ≤ C.card).card := rfl
      have e2 : wideCount W md2 = (md2.lines.filter fun C => W ≤ C.card).card := rfl
      -- Either a wide line dies or none existed; both leave at most s.
      have hcount2 : wideCount W md2 ≤ s := by
        rcases Nat.eq_zero_or_pos (wideCount W md1) with h0 | h0
        · -- Nothing wide: the restriction keeps the count at zero.
          have hz : (md1.lines.filter fun C => W ≤ C.card).card = 0 := by
            rw [← e1]
            exact h0
          have hle0 : (md2.lines.filter fun C => W ≤ C.card).card ≤ 0 := by
            have h' := hcut
            rw [hz] at h'
            simpa using h'
          rw [e2]
          exact le_trans hle0 (Nat.zero_le s)
        · -- Something wide dies, leaving at most s.
          have h0' : 0 < (md1.lines.filter fun C => W ≤ C.card).card := by
            rw [← e1]
            exact h0
          have hst := hstrict h0'
          have hle : (md1.lines.filter fun C => W ≤ C.card).card ≤ s + 1 := by
            rw [← e1, hcount1]
            exact hcount
          rw [e2]
          exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hst hle)
      obtain ⟨md3, hs3, hcount3⟩ := ih k (by omega) md2 hcount2
      have hk' : k - s = n - (s + 1) := by omega
      obtain ⟨md4, hs4, hl4⟩ := exists_monoDeriv_of_scale_eq hk' md3
      refine ⟨md4, by omega, ?_⟩
      simp only [wideCount, hl4] at hcount3 ⊢
      exact hcount3

/-- Wipeout: enough dense steps followed by a sparse tail remove every `W`
wide line, shrinking PHP by `t + s` pigeons and never growing the size. -/
theorem exists_monoDeriv_wipeout {W V₀ : ℕ} (hW : 0 < W) (hV₀ : 0 < V₀)
    {t s n : ℕ} (hts : t + s ≤ n)
    (huni : ∀ k, k < n → (k + 2) * (k + 1) ≤ V₀)
    (md : MonoDeriv n (∅ : Clause))
    (hafter : (2 * V₀ - W) ^ t * (wideCount W md * W) + (2 * V₀) ^ t * V₀ ≤
      (2 * V₀) ^ t * (s * W)) :
    ∃ md' : MonoDeriv (n - (t + s)) (∅ : Clause),
      md'.size ≤ md.size ∧ wideCount W md' = 0 := by
  obtain ⟨md1, hs1, hinv⟩ := exists_monoDeriv_iter hW hV₀ t n (by omega) huni md
  -- Cancel the positive factors to bound the surviving wide count by s.
  have hcount : wideCount W md1 ≤ s := by
    have hchain : (2 * V₀) ^ t * (wideCount W md1 * W) ≤
        (2 * V₀) ^ t * (s * W) := le_trans hinv hafter
    have hpow : 0 < (2 * V₀) ^ t := by positivity
    have h1 : wideCount W md1 * W ≤ s * W :=
      Nat.le_of_mul_le_mul_left hchain hpow
    exact Nat.le_of_mul_le_mul_right h1 hW
  obtain ⟨md2, hs2, hzero⟩ :=
    exists_monoDeriv_tail hW s (n - t) (by omega) md1 hcount
  have heq : n - t - s = n - (t + s) := by omega
  obtain ⟨md3, hs3, hl3⟩ := exists_monoDeriv_of_scale_eq heq md2
  refine ⟨md3, by omega, ?_⟩
  simp only [wideCount, hl3] at hzero ⊢
  exact hzero

/-! ## G8g: final counting and honest size lower bound

Pin the width threshold at the terminal scale `m = n / 2`, take volume
uniformizer `V₀ = (n+1)*n`, and choose a sparse budget `s` covering the stuck
term. Wipeout then contradicts `exists_wide_line` at scale `m` whenever the
starting size is smaller than the dense-phase growth. The certified width
`((m+1)/3)²` and the halved rate in `kill_step_mul` yield an honest exponential
`2^(n/50)`, weaker than the paper / Frontier `2^(n/20)`.
-/

/-- Wide count never exceeds derivation size. -/
theorem wideCount_le_size (W : ℕ) {n : ℕ} {C : Clause} (md : MonoDeriv n C) :
    wideCount W md ≤ md.size :=
  (card_filter_le _ _).trans md.lines_card_le_size

/-- Grid volumes are monotone in the scale. -/
theorem gridVol_le {k n : ℕ} (hk : k ≤ n) :
    (k + 1) * k ≤ (n + 1) * n := by
  have h1 : k ≤ n := hk
  have h2 : k + 1 ≤ n + 1 := by omega
  exact Nat.mul_le_mul h2 h1

/-- Every scale below `n` has volume at most `(n+1)*n`. -/
theorem gridVol_lt_le (n : ℕ) {k : ℕ} (hk : k < n) :
    (k + 2) * (k + 1) ≤ (n + 1) * n := by
  have : k + 1 ≤ n := by omega
  simpa [Nat.succ_mul] using gridVol_le (k := k + 1) this

/-- Algebraic wipeout hypothesis from a size bound and a sparse budget. -/
theorem wipeout_hyp_of_size_le {W V₀ S t s : ℕ}
    (_hW : 0 < W) (_hV₀ : 0 < V₀)
    (hs : 2 * V₀ ≤ s * W)
    (hS : S * W * (2 * V₀ - W) ^ t ≤ V₀ * (2 * V₀) ^ t) :
    (2 * V₀ - W) ^ t * (S * W) + (2 * V₀) ^ t * V₀ ≤
      (2 * V₀) ^ t * (s * W) := by
  have h1 : (2 * V₀ - W) ^ t * (S * W) ≤ (2 * V₀) ^ t * V₀ := by
    -- rearrange hS
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hS
  have h2 : (2 * V₀) ^ t * V₀ + (2 * V₀) ^ t * V₀ ≤ (2 * V₀) ^ t * (s * W) := by
    have : V₀ + V₀ ≤ s * W := by
      have := hs
      omega
    calc (2 * V₀) ^ t * V₀ + (2 * V₀) ^ t * V₀
        = (2 * V₀) ^ t * (V₀ + V₀) := by ring
      _ ≤ (2 * V₀) ^ t * (s * W) := Nat.mul_le_mul_left _ this
  calc (2 * V₀ - W) ^ t * (S * W) + (2 * V₀) ^ t * V₀
      ≤ (2 * V₀) ^ t * V₀ + (2 * V₀) ^ t * V₀ := Nat.add_le_add_right h1 _
    _ ≤ (2 * V₀) ^ t * (s * W) := h2

/-- Wipeout to the terminal scale contradicts the forced wide line. -/
theorem wipeout_contradicts_wide_line {W V₀ : ℕ} (hW : 0 < W) (hV₀ : 0 < V₀)
    {t s n : ℕ} (hts : t + s ≤ n)
    (huni : ∀ k, k < n → (k + 2) * (k + 1) ≤ V₀)
    (md : MonoDeriv n (∅ : Clause))
    (hafter : (2 * V₀ - W) ^ t * (wideCount W md * W) + (2 * V₀) ^ t * V₀ ≤
      (2 * V₀) ^ t * (s * W))
    (hm : 1 ≤ n - (t + s))
    (hWterm : W = largeThreshold (n - (t + s))) :
    False := by
  obtain ⟨md', _, hzero⟩ :=
    exists_monoDeriv_wipeout hW hV₀ hts huni md hafter
  obtain ⟨C', hmem, hcard⟩ := MonoDeriv.exists_wide_line hm md'
  have hwide : W ≤ C'.card := by
    rw [hWterm]
    exact hcard
  have hpos : 0 < wideCount W md' := by
    refine card_pos.mpr ⟨C', mem_filter.mpr ⟨hmem, hwide⟩⟩
  omega

/-- Ratio hypothesis `V₀ ≤ 18 W` yields the `36/35` growth factor on `2V` vs
`2V−W`. -/
theorem growth_ratio_of_width {V₀ W : ℕ} (_hV₀ : 0 < V₀)
    (hwid : V₀ ≤ 18 * W) :
    36 * (2 * V₀ - W) ≤ 35 * (2 * V₀) := by
  omega

/-- For `n ≥ 200`, the top grid volume is at most 18 times the terminal
threshold at scale `3n/4`. -/
theorem volume_le_eighteen_threshold {n : ℕ} (hn : 200 ≤ n) :
    (n + 1) * n ≤ 18 * largeThreshold (3 * n / 4) := by
  have hq' : 50 ≤ n / 4 := by omega
  have hquot : n / 4 ≤ (3 * n / 4 + 1) / 3 := by omega
  have hW : (n / 4) * (n / 4) ≤ largeThreshold (3 * n / 4) := by
    simp only [largeThreshold]
    exact Nat.mul_le_mul hquot hquot
  have hnbound : n ≤ 4 * (n / 4) + 3 := by omega
  have hprod : (n + 1) * n ≤ (4 * (n / 4) + 4) * (4 * (n / 4) + 3) :=
    Nat.mul_le_mul (by omega) hnbound
  have hexpand :
      (4 * (n / 4) + 4) * (4 * (n / 4) + 3) =
        16 * (n / 4) * (n / 4) + 28 * (n / 4) + 12 := by
    ring
  have hcalc :
      16 * (n / 4) * (n / 4) + 28 * (n / 4) + 12 ≤ 18 * ((n / 4) * (n / 4)) := by
    set q := n / 4
    have hq50 : 50 ≤ q := hq'
    have h2q : 100 ≤ 2 * q := by omega
    have hsq : 100 * q ≤ 2 * q * q := Nat.mul_le_mul_right q h2q
    have hlin : 28 * q + 12 ≤ 100 * q := by omega
    have : 28 * q + 12 ≤ 2 * q * q := le_trans hlin hsq
    -- 16q*q + 28q + 12 ≤ 16q*q + 2q*q = 18q*q
    have hleft : 16 * q * q + 28 * q + 12 ≤ 16 * q * q + 2 * q * q := by omega
    have hright : 16 * q * q + 2 * q * q = 18 * (q * q) := by ring
    exact hleft.trans_eq hright
  have hV : (n + 1) * n ≤ 18 * ((n / 4) * (n / 4)) := by
    calc (n + 1) * n
        ≤ (4 * (n / 4) + 4) * (4 * (n / 4) + 3) := hprod
      _ = 16 * (n / 4) * (n / 4) + 28 * (n / 4) + 12 := hexpand
      _ ≤ 18 * ((n / 4) * (n / 4)) := hcalc
  exact le_trans hV (Nat.mul_le_mul_left _ hW)

end SATurday.ProofComplexity
