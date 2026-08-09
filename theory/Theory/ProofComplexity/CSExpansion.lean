import Theory.ProofComplexity.Width
import Theory.ProofComplexity.SizeWidth

/-!
# Chvatal–Szemeredi expansion for k-CNF (Ladder Rung R2, item 2)

Pinned API from docs/ladder/rungs/r2-width-machinery.md: `boundaryClauses`,
`HasCSExpansion`, `csWidthDiv`, `cs_expansion_width_lower_bound`. Reuses
certified `cnfWidth` / `cnfVars` and the BSW size machine from SizeWidth.lean.

Cluster 2 builds the clause-complex bridge (same skeleton as Tseitin, with
`boundaryClauses` in place of `edgeBoundary`). Existence
`exists_cs_expanding_3cnf` remains a hard probabilistic gap.

LOG: R2 CSExpansion complex bridge and width LB
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Clause and CNF supports -/

/-- Variable support of a clause (alias of `clauseVars` for CS packaging). -/
abbrev clauseSupport (C : Clause) : Finset ℕ := clauseVars C

/-- Variable support of a CNF (alias of `cnfVars`). -/
abbrev cnfSupport (F : CNF) : Finset ℕ := cnfVars F

/-! ## Boundary clauses -/

/-- Clauses of `F` that touch both `S` and its complement inside `cnfVars F`. -/
def boundaryClauses (F : CNF) (S : Finset ℕ) : Finset Clause :=
  F.filter fun C =>
    (clauseSupport C ∩ S).Nonempty ∧
      (clauseSupport C ∩ (cnfSupport F \ S)).Nonempty

/-- Boundary clauses are hypotheses of `F`. -/
theorem boundaryClauses_subset (F : CNF) (S : Finset ℕ) :
    boundaryClauses F S ⊆ F :=
  filter_subset _ _

theorem mem_boundaryClauses_iff (F : CNF) (S : Finset ℕ) (C : Clause) :
    C ∈ boundaryClauses F S ↔
      C ∈ F ∧
        (clauseSupport C ∩ S).Nonempty ∧
          (clauseSupport C ∩ (cnfSupport F \ S)).Nonempty := by
  simp [boundaryClauses]

/-- Empty support has empty CS boundary. -/
theorem boundaryClauses_empty (F : CNF) :
    boundaryClauses F (∅ : Finset ℕ) = ∅ := by
  ext C
  simp [boundaryClauses]

/-- Full CNF support has empty CS boundary. -/
theorem boundaryClauses_cnfSupport (F : CNF) :
    boundaryClauses F (cnfSupport F) = ∅ := by
  ext C
  simp [boundaryClauses]

/-! ## CS expansion hypothesis -/

/-- Discrete Chvatal–Szemeredi style expansion: width at most `k`, and every
nonempty `S ⊆ cnfVars F` with `β * S.card ≤ (cnfVars F).card` has at least
`α * S.card` boundary clauses. -/
def HasCSExpansion (F : CNF) (k β α : ℕ) : Prop :=
  cnfWidth F ≤ k ∧
    ∀ S : Finset ℕ, S ⊆ cnfSupport F → S.Nonempty →
      β * S.card ≤ (cnfSupport F).card →
        α * S.card ≤ (boundaryClauses F S).card

/-- Width side of the CS hypothesis. -/
theorem HasCSExpansion.cnfWidth_le {F : CNF} {k β α : ℕ}
    (h : HasCSExpansion F k β α) : cnfWidth F ≤ k :=
  h.1

/-- Boundary side of the CS hypothesis. -/
theorem HasCSExpansion.boundary_ge {F : CNF} {k β α : ℕ}
    (h : HasCSExpansion F k β α) {S : Finset ℕ}
    (hS : S ⊆ cnfSupport F) (hne : S.Nonempty)
    (hβ : β * S.card ≤ (cnfSupport F).card) :
    α * S.card ≤ (boundaryClauses F S).card :=
  h.2 S hS hne hβ

/-- Reserved CS width divisor (pinned). -/
def csWidthDiv : ℕ := 2

theorem csWidthDiv_eq : csWidthDiv = 2 := rfl

/-- Informative CS width floor under the pinned packaging. -/
def csWidthFloor (n β α : ℕ) : ℕ := (α * n) / (csWidthDiv * β)

/-- Pinned target shape (statement only packaging): under `HasCSExpansion`,
every refutation has width at least `csWidthFloor`. Full proof is the next
cluster (clause-complex growth); this records the exact inequality demanded
by the pin so later cycles cannot drift. -/
def CSExpansionWidthLowerBoundStatement (F : CNF) (k β α : ℕ) : Prop :=
  HasCSExpansion F k β α →
    ∀ d : Derivation F (∅ : Clause),
      csWidthFloor (cnfSupport F).card β α ≤ d.width

/-- Size corollary shape: BSW applied at the CS width floor. -/
def CSExpansionSizeLowerBoundStatement (F : CNF) (k β α : ℕ) : Prop :=
  HasCSExpansion F k β α →
    ∀ d : Derivation F (∅ : Clause),
      let W := csWidthFloor (cnfSupport F).card β α
      2 ^ ((W - cnfWidth F) * (W - cnfWidth F) /
            (bswRateConst * (cnfVars F).card)) ≤ d.size

/-- Trivial case: if the CS floor is 0 then the width claim holds. -/
theorem cs_expansion_width_lower_bound_of_floor_zero {F : CNF} {k β α : ℕ}
    (hfloor : csWidthFloor (cnfSupport F).card β α = 0)
    (_h : HasCSExpansion F k β α)
    (d : Derivation F (∅ : Clause)) :
    csWidthFloor (cnfSupport F).card β α ≤ d.width := by
  simp [hfloor]

/-- When `β = 0` the floor packaging is undefined for informativeness; record
that the divisor product vanishes so the floor is 0. -/
theorem csWidthFloor_beta_zero (n α : ℕ) :
    csWidthFloor n 0 α = 0 := by
  simp [csWidthFloor, csWidthDiv]

/-- Singleton boundary: a clause that mixes one variable of `S` with one outside. -/
theorem singleton_mem_boundaryClauses {F : CNF} {x y : ℕ} {C : Clause}
    (hy : y ∈ cnfSupport F) (hne : x ≠ y)
    (hC : C ∈ F) (hxC : x ∈ clauseSupport C) (hyC : y ∈ clauseSupport C) :
    C ∈ boundaryClauses F ({x} : Finset ℕ) := by
  refine (mem_boundaryClauses_iff F ({x} : Finset ℕ) C).mpr ⟨hC, ?_, ?_⟩
  · exact ⟨x, mem_inter.mpr ⟨hxC, mem_singleton_self x⟩⟩
  · refine ⟨y, mem_inter.mpr ⟨hyC, mem_sdiff.mpr ⟨hy, ?_⟩⟩⟩
    simp [hne.symm]

/-- CS boundary is unchanged when `S` is replaced by its complement in the support. -/
theorem boundaryClauses_sdiff_support (F : CNF) (S : Finset ℕ)
    (hS : S ⊆ cnfSupport F) :
    boundaryClauses F S = boundaryClauses F (cnfSupport F \ S) := by
  ext C
  simp only [mem_boundaryClauses_iff]
  constructor
  · rintro ⟨hC, hIn, hOut⟩
    refine ⟨hC, ?_, ?_⟩
    · -- old outside becomes new inside
      obtain ⟨x, hx⟩ := hOut
      exact ⟨x, by
        have hxC : x ∈ clauseSupport C := (mem_inter.mp hx).1
        have hxSupp : x ∈ cnfSupport F \ S := (mem_inter.mp hx).2
        exact mem_inter.mpr ⟨hxC, hxSupp⟩⟩
    · obtain ⟨y, hy⟩ := hIn
      have hyC : y ∈ clauseSupport C := (mem_inter.mp hy).1
      have hyS : y ∈ S := (mem_inter.mp hy).2
      have hySupp : y ∈ cnfSupport F := hS hyS
      refine ⟨y, mem_inter.mpr ⟨hyC, mem_sdiff.mpr ⟨hySupp, ?_⟩⟩⟩
      intro hyIn
      exact (mem_sdiff.mp hyIn).2 hyS
  · rintro ⟨hC, hIn, hOut⟩
    refine ⟨hC, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := hOut
      have hyC : y ∈ clauseSupport C := (mem_inter.mp hy).1
      have hyNot : y ∈ cnfSupport F \ (cnfSupport F \ S) := (mem_inter.mp hy).2
      have hyS : y ∈ S := by
        have : y ∈ cnfSupport F ∧ y ∉ cnfSupport F \ S := mem_sdiff.mp hyNot
        by_contra hny
        exact this.2 (mem_sdiff.mpr ⟨this.1, hny⟩)
      exact ⟨y, mem_inter.mpr ⟨hyC, hyS⟩⟩
    · obtain ⟨x, hx⟩ := hIn
      exact ⟨x, by
        have hxC : x ∈ clauseSupport C := (mem_inter.mp hx).1
        have hxSupp : x ∈ cnfSupport F \ S := (mem_inter.mp hx).2
        exact mem_inter.mpr ⟨hxC, hxSupp⟩⟩

/-- Floor packaging with `α = 0` is identically zero. -/
theorem csWidthFloor_alpha_zero (n β : ℕ) :
    csWidthFloor n β 0 = 0 := by
  simp [csWidthFloor]

/-- Positive CS floor requires positive parameters and large enough support. -/
theorem csWidthFloor_pos_iff (n β α : ℕ) (hβ : 0 < β) :
    0 < csWidthFloor n β α ↔ csWidthDiv * β ≤ α * n := by
  simp only [csWidthFloor, csWidthDiv]
  have hden : 0 < 2 * β := Nat.mul_pos (by decide : (0 : ℕ) < 2) hβ
  constructor
  · intro h
    simpa using (Nat.le_div_iff_mul_le hden).1 (Nat.succ_le_of_lt h)
  · intro h
    exact Nat.div_pos h hden

/-- Trivial CS expansion when `α = 0`: width bound plus vacuous boundary. -/
theorem HasCSExpansion.alpha_zero {F : CNF} {k β : ℕ}
    (hw : cnfWidth F ≤ k) : HasCSExpansion F k β 0 :=
  ⟨hw, fun S _ _ _ => by simp⟩

/-- Width LB statement holds under `α = 0` (floor vanishes). -/
theorem cs_expansion_width_lower_bound_alpha_zero {F : CNF} {k β : ℕ}
    (_h : HasCSExpansion F k β 0)
    (d : Derivation F (∅ : Clause)) :
    csWidthFloor (cnfSupport F).card β 0 ≤ d.width := by
  simp [csWidthFloor_alpha_zero]

/-! ## Semantic CS complexes (clause boundary form of the Tseitin bridge) -/

/-- Sub-CNF of clauses entirely supported on `S`. -/
def csSubCNF (F : CNF) (S : Finset ℕ) : CNF :=
  F.filter fun C => clauseSupport C ⊆ S

theorem mem_csSubCNF_iff (F : CNF) (S : Finset ℕ) (C : Clause) :
    C ∈ csSubCNF F S ↔ C ∈ F ∧ clauseSupport C ⊆ S := by
  simp [csSubCNF]

/-- Variable set `S` semantically implies clause `C` from the sub-CNF on `S`. -/
def csImplies (F : CNF) (S : Finset ℕ) (C : Clause) : Prop :=
  ∀ a : Assignment, cnfSat a (csSubCNF F S) → clauseSat a C

/-- Erase-minimal implying variable set. -/
def IsEraseMinimalCSComplex (F : CNF) (S : Finset ℕ) (C : Clause) : Prop :=
  csImplies F S C ∧ ∀ x ∈ S, ¬ csImplies F (S.erase x) C

/-- Every implying set has an erase-minimal subset. -/
theorem exists_eraseMinimalCSComplex {F : CNF} {C : Clause}
    (S : Finset ℕ) (h : csImplies F S C) :
    ∃ T ⊆ S, IsEraseMinimalCSComplex F T C := by
  classical
  revert h
  refine Finset.strongInductionOn S ?_
  intro S IH h
  by_cases hmin : ∀ x ∈ S, ¬ csImplies F (S.erase x) C
  · exact ⟨S, subset_rfl, h, hmin⟩
  · simp only [not_forall, Classical.not_imp, not_not] at hmin
    obtain ⟨x, hx, hximp⟩ := hmin
    obtain ⟨T, hTsub, hTmin⟩ := IH (S.erase x) (erase_ssubset hx) hximp
    exact ⟨T, hTsub.trans (erase_subset x S), hTmin⟩

noncomputable def chooseEraseMinimalCSComplex {F : CNF} {C : Clause}
    (S : Finset ℕ) (h : csImplies F S C) : Finset ℕ :=
  Classical.choose (exists_eraseMinimalCSComplex S h)

theorem chooseEraseMinimalCSComplex_subset {F : CNF} {C : Clause}
    (S : Finset ℕ) (h : csImplies F S C) :
    chooseEraseMinimalCSComplex S h ⊆ S :=
  (Classical.choose_spec (exists_eraseMinimalCSComplex S h)).1

theorem chooseEraseMinimalCSComplex_isMinimal {F : CNF} {C : Clause}
    (S : Finset ℕ) (h : csImplies F S C) :
    IsEraseMinimalCSComplex F (chooseEraseMinimalCSComplex S h) C :=
  (Classical.choose_spec (exists_eraseMinimalCSComplex S h)).2

/-- Boundary clauses meet the variables of `C`. -/
def boundaryCovered (F : CNF) (S : Finset ℕ) (C : Clause) : Prop :=
  ∀ B ∈ boundaryClauses F S, (clauseSupport B ∩ clauseVars C).Nonempty

/-- Hypothesis clause is implied by its own support. -/
theorem csImplies_hyp {F : CNF} {C : Clause} (hC : C ∈ F) :
    csImplies F (clauseSupport C) C := by
  intro a ha
  exact ha C ((mem_csSubCNF_iff F _ C).mpr ⟨hC, subset_rfl⟩)

/-- Implication preserved by resolution on the union of supports. -/
theorem csImplies_resolvent {F : CNF} {C D : Clause} (x : ℕ) {S T : Finset ℕ}
    (hC : csImplies F S C) (hD : csImplies F T D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    csImplies F (S ∪ T) (resolvent C D x) := by
  intro a ha
  have haS : cnfSat a (csSubCNF F S) := by
    intro E hE
    obtain ⟨hEF, hsup⟩ := (mem_csSubCNF_iff F S E).mp hE
    exact ha E ((mem_csSubCNF_iff F (S ∪ T) E).mpr
      ⟨hEF, hsup.trans subset_union_left⟩)
  have haT : cnfSat a (csSubCNF F T) := by
    intro E hE
    obtain ⟨hEF, hsup⟩ := (mem_csSubCNF_iff F T E).mp hE
    exact ha E ((mem_csSubCNF_iff F (S ∪ T) E).mpr
      ⟨hEF, hsup.trans subset_union_right⟩)
  have hCs : clauseSat a C := hC a haS
  have hDs : clauseSat a D := hD a haT
  by_cases hax : a x = true
  · obtain ⟨l, hl, hla⟩ := hDs
    have hlne : l ≠ ⟨x, false⟩ := by
      intro heq
      have : a x = false := by simpa [heq, litSat] using hla
      exact Bool.false_ne_true (this.symm.trans hax)
    exact ⟨l, mem_union.mpr (Or.inr (mem_erase.mpr ⟨hlne, hl⟩)), hla⟩
  · obtain ⟨l, hl, hla⟩ := hCs
    have hlne : l ≠ ⟨x, true⟩ := by
      intro heq
      have : a x = true := by simpa [heq, litSat] using hla
      exact hax this
    exact ⟨l, mem_union.mpr (Or.inl (mem_erase.mpr ⟨hlne, hl⟩)), hla⟩

/-- Support of any clause of `F` lies in `cnfSupport F`. -/
theorem clauseSupport_subset_cnfSupport {F : CNF} {C : Clause} (hC : C ∈ F) :
    clauseSupport C ⊆ cnfSupport F := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
  exact mem_cnfVars.mpr ⟨C, hC, l, hl, rfl⟩

/-! ## Derivation-indexed CS complexes -/

structure Derivation.CSComplexData {F : CNF} {C : Clause} (d : Derivation F C) where
  S : Finset ℕ
  isMinimal : IsEraseMinimalCSComplex F S C

noncomputable def Derivation.csComplexData {F : CNF} :
    {C : Clause} → (d : Derivation F C) → Derivation.CSComplexData d
  | C, .hyp _ hC =>
    ⟨chooseEraseMinimalCSComplex (clauseSupport C) (csImplies_hyp hC),
      chooseEraseMinimalCSComplex_isMinimal (clauseSupport C) (csImplies_hyp hC)⟩
  | _, .res x dC dD hx hnx =>
    let pC := dC.csComplexData
    let pD := dD.csComplexData
    let hU := csImplies_resolvent x pC.isMinimal.1 pD.isMinimal.1 hx hnx
    ⟨chooseEraseMinimalCSComplex (pC.S ∪ pD.S) hU,
      chooseEraseMinimalCSComplex_isMinimal (pC.S ∪ pD.S) hU⟩

noncomputable def Derivation.csComplex {F : CNF} {C : Clause}
    (d : Derivation F C) : Finset ℕ :=
  d.csComplexData.S

theorem csComplex_isMinimal {F : CNF} {C : Clause} (d : Derivation F C) :
    IsEraseMinimalCSComplex F d.csComplex C :=
  d.csComplexData.isMinimal

theorem csComplex_implies {F : CNF} {C : Clause} (d : Derivation F C) :
    csImplies F d.csComplex C :=
  (csComplex_isMinimal d).1

theorem csComplex_subset_cnfSupport {F : CNF} {C : Clause} (d : Derivation F C) :
    d.csComplex ⊆ cnfSupport F := by
  induction d with
  | hyp C hC =>
    intro x hx
    simp only [Derivation.csComplex, Derivation.csComplexData] at hx
    have hsub :=
      chooseEraseMinimalCSComplex_subset (clauseSupport C) (csImplies_hyp hC)
    exact clauseSupport_subset_cnfSupport hC (hsub hx)
  | res x dC dD hx hnx ihC ihD =>
    intro y hy
    simp only [Derivation.csComplex, Derivation.csComplexData] at hy
    have hU := csImplies_resolvent x dC.csComplexData.isMinimal.1
      dD.csComplexData.isMinimal.1 hx hnx
    have hsub :=
      chooseEraseMinimalCSComplex_subset (dC.csComplexData.S ∪ dD.csComplexData.S) hU
    have hy' : y ∈ dC.csComplexData.S ∪ dD.csComplexData.S := hsub hy
    rcases mem_union.mp hy' with h | h
    · exact ihC (by simpa [Derivation.csComplex] using h)
    · exact ihD (by simpa [Derivation.csComplex] using h)

theorem csComplex_res_subset {F : CNF} {C D : Clause} (x : ℕ)
    (dC : Derivation F C) (dD : Derivation F D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    (Derivation.res x dC dD hx hnx).csComplex ⊆
      dC.csComplex ∪ dD.csComplex := by
  have hU := csImplies_resolvent x dC.csComplexData.isMinimal.1
    dD.csComplexData.isMinimal.1 hx hnx
  simp only [Derivation.csComplex, Derivation.csComplexData]
  exact chooseEraseMinimalCSComplex_subset (dC.csComplexData.S ∪ dD.csComplexData.S) hU

/-- Empty clause is never satisfied. -/
theorem not_clauseSat_empty_cs (a : Assignment) : ¬ clauseSat a (∅ : Clause) := by
  simp [clauseSat]

/-- The CS sub-CNF on an erase-minimal complex for `∅` is unsatisfiable. -/
theorem csSubCNF_unsat_of_eraseMinimal_empty {F : CNF} {S : Finset ℕ}
    (hmin : IsEraseMinimalCSComplex F S (∅ : Clause)) :
    ¬ ∃ a, cnfSat a (csSubCNF F S) := by
  rintro ⟨a, ha⟩
  exact not_clauseSat_empty_cs a (hmin.1 a ha)

/-- Size corollary packaging once the width LB is available. -/
theorem cs_expansion_size_lower_bound_of_width {F : CNF} {k β α : ℕ}
    (h : HasCSExpansion F k β α)
    (hw : ∀ d : Derivation F (∅ : Clause),
      csWidthFloor (cnfSupport F).card β α ≤ d.width)
    (d : Derivation F (∅ : Clause)) :
    let W := csWidthFloor (cnfSupport F).card β α
    2 ^ ((W - cnfWidth F) * (W - cnfWidth F) /
          (bswRateConst * (cnfVars F).card)) ≤ d.size := by
  intro W
  exact bsw_size_lower_bound F W hw d

/-! ## Frontier: remaining bridge obligations for the pinned width LB -/

namespace CSExpansionFrontier

/-- Stuck obligation (cycle 2026-08-09): erase-minimal complexes are
boundary-covered, with an injective variable selection so that
`(boundaryClauses F S).card ≤ C.card`. The Tseitin flip uses edge variables;
the CS flip needs a clause-crossing variable argument. -/
theorem boundaryCovered_of_eraseMinimal {F : CNF} {S : Finset ℕ} {C : Clause}
    (hmin : IsEraseMinimalCSComplex F S C) :
    boundaryCovered F S C := by
  sorry

/-- Stuck obligation: medium-line extraction from a large CS complex for `∅`,
parallel to `exists_medium_tseitin_complex`. -/
theorem exists_medium_cs_complex {F : CNF} {β : ℕ}
    (d : Derivation F (∅ : Clause)) (hβ : 0 < β)
    (hLarge : (cnfSupport F).card / β < d.csComplex.card) :
    ∃ (C : Clause) (dC : Derivation F C),
      dC.csComplex.card ≤ (cnfSupport F).card / β ∧
        csWidthFloor (cnfSupport F).card β 1 ≤ dC.csComplex.card ∧
          dC.width ≤ d.width ∧
            boundaryCovered F dC.csComplex C := by
  sorry

/-- Pinned width LB (Frontier until coverage and medium extraction close). -/
theorem cs_expansion_width_lower_bound {F : CNF} {k β α : ℕ}
    (h : HasCSExpansion F k β α) (_hα : 1 ≤ α) (_hβ : 0 < β)
    (d : Derivation F (∅ : Clause)) :
    csWidthFloor (cnfSupport F).card β α ≤ d.width := by
  sorry

/-- Pinned existence gap (probabilistic method; not this cycle). -/
theorem exists_cs_expanding_3cnf :
    ∀ N : ℕ, ∃ (n : ℕ) (F : CNF) (β α : ℕ),
      N ≤ n ∧ (cnfVars F).card = n ∧ β = 4 ∧ α = 1 ∧
        HasCSExpansion F 3 β α ∧ ¬ Satisfiable F ∧
          cnfWidth F < csWidthFloor n β α := by
  sorry

end CSExpansionFrontier

end SATurday.ProofComplexity
