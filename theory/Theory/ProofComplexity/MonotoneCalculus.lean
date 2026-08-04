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

end SATurday.ProofComplexity
