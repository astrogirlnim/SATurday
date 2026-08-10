import Theory.ProofComplexity.Width
import Theory.ProofComplexity.SizeWidth

/-!
# Chvatal–Szemeredi expansion for k-CNF (Ladder Rung R2, item 2)

Critical path (pin restated 2026-08-09): `IsCSMatchable`, `HasCSClauseExpansion`,
`csClauseWidthFloor`, certified `cs_clause_expansion_width_lower_bound`.
Existence target: `exists_cs_clause_expanding_3cnf` (Frontier).
Accepted reduction: `Spreads` at rate 2 plus width ≤ 3 yields
`hasCSClauseExpansion_one_of_spreads_two`.

Demoted (not critical path): variable-side `HasCSExpansion` / `boundaryClauses`
and Frontier `cs_expansion_width_lower_bound` / obsolete `exists_cs_expanding_3cnf`.

Reuses certified `cnfWidth` / `cnfVars` and the BSW size machine from SizeWidth.
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

/-! ## BSW clause-set complexes (μ-measure)

The standard random k-CNF width argument (Ben-Sasson and Wigderson) uses the
size of a minimal *axiom set* implying a derived clause, with boundary equal to
variables appearing in exactly one axiom of that set. Coverage: each boundary
variable lies in the derived clause (OR sensitivity + critical assignment). -/

/-- Variables appearing in exactly one clause of `G`. -/
def clauseSetBoundary (G : Finset Clause) : Finset ℕ :=
  (G.biUnion clauseSupport).filter fun x =>
    (G.filter fun C => x ∈ clauseSupport C).card = 1

theorem mem_clauseSetBoundary_iff (G : Finset Clause) (x : ℕ) :
    x ∈ clauseSetBoundary G ↔
      x ∈ G.biUnion clauseSupport ∧
        (G.filter fun C => x ∈ clauseSupport C).card = 1 := by
  simp [clauseSetBoundary]

/-- Axiom set `G ⊆ F` semantically implies `C`. -/
def csClauseImplies (F : CNF) (G : Finset Clause) (C : Clause) : Prop :=
  G ⊆ F ∧ ∀ a : Assignment, cnfSat a G → clauseSat a C

/-- Erase-minimal axiom complex for `C`. -/
def IsEraseMinimalClauseComplex (F : CNF) (G : Finset Clause) (C : Clause) : Prop :=
  csClauseImplies F G C ∧ ∀ D ∈ G, ¬ csClauseImplies F (G.erase D) C

theorem exists_eraseMinimalClauseComplex {F : CNF} {C : Clause}
    (G : Finset Clause) (h : csClauseImplies F G C) :
    ∃ H ⊆ G, IsEraseMinimalClauseComplex F H C := by
  classical
  revert h
  refine Finset.strongInductionOn G ?_
  intro G IH h
  by_cases hmin : ∀ D ∈ G, ¬ csClauseImplies F (G.erase D) C
  · exact ⟨G, subset_rfl, h, hmin⟩
  · simp only [not_forall, Classical.not_imp, not_not] at hmin
    obtain ⟨D, hD, hDimp⟩ := hmin
    obtain ⟨H, hHsub, hHmin⟩ := IH (G.erase D) (erase_ssubset hD) hDimp
    exact ⟨H, hHsub.trans (erase_subset D G), hHmin⟩

noncomputable def chooseEraseMinimalClauseComplex {F : CNF} {C : Clause}
    (G : Finset Clause) (h : csClauseImplies F G C) : Finset Clause :=
  Classical.choose (exists_eraseMinimalClauseComplex G h)

theorem chooseEraseMinimalClauseComplex_subset {F : CNF} {C : Clause}
    (G : Finset Clause) (h : csClauseImplies F G C) :
    chooseEraseMinimalClauseComplex G h ⊆ G :=
  (Classical.choose_spec (exists_eraseMinimalClauseComplex G h)).1

theorem chooseEraseMinimalClauseComplex_isMinimal {F : CNF} {C : Clause}
    (G : Finset Clause) (h : csClauseImplies F G C) :
    IsEraseMinimalClauseComplex F (chooseEraseMinimalClauseComplex G h) C :=
  (Classical.choose_spec (exists_eraseMinimalClauseComplex G h)).2

/-- Flip one variable. -/
def csFlipVar (a : Assignment) (x : ℕ) : Assignment :=
  fun y => if y = x then !a y else a y

theorem clauseSat_csFlipVar_of_not_mem (a : Assignment) (C : Clause) (x : ℕ)
    (hx : x ∉ clauseVars C) :
    clauseSat (csFlipVar a x) C ↔ clauseSat a C := by
  classical
  constructor
  · rintro ⟨l, hl, hlit⟩
    refine ⟨l, hl, ?_⟩
    have hvar : l.var ≠ x := by
      intro heq
      exact hx (mem_image.mpr ⟨l, hl, heq⟩)
    simpa [litSat, csFlipVar, hvar] using hlit
  · rintro ⟨l, hl, hlit⟩
    refine ⟨l, hl, ?_⟩
    have hvar : l.var ≠ x := by
      intro heq
      exact hx (mem_image.mpr ⟨l, hl, heq⟩)
    simpa [litSat, csFlipVar, hvar] using hlit

theorem cnfSat_csFlipVar_of_not_mem_supports (a : Assignment) (G : Finset Clause)
    (x : ℕ) (hx : ∀ C ∈ G, x ∉ clauseSupport C) :
    cnfSat (csFlipVar a x) G ↔ cnfSat a G := by
  classical
  constructor
  · intro ha C hC
    exact (clauseSat_csFlipVar_of_not_mem a C x (hx C hC)).1 (ha C hC)
  · intro ha C hC
    exact (clauseSat_csFlipVar_of_not_mem a C x (hx C hC)).2 (ha C hC)

/-- BSW coverage: boundary variables of an erase-minimal axiom complex lie in `C`.
Critical assignment for the unique owner clause plus OR sensitivity under flip. -/
theorem clauseSetBoundary_subset_clauseVars {F : CNF} {G : Finset Clause} {C : Clause}
    (hmin : IsEraseMinimalClauseComplex F G C) :
    clauseSetBoundary G ⊆ clauseVars C := by
  classical
  intro x hx
  by_contra hxC
  have hcard : (G.filter fun D => x ∈ clauseSupport D).card = 1 :=
    (mem_clauseSetBoundary_iff G x |>.mp hx).2
  obtain ⟨D, hDsing⟩ := card_eq_one.mp hcard
  have hDfilt : D ∈ G.filter fun E => x ∈ clauseSupport E := by
    simp [hDsing]
  have hDG : D ∈ G := (mem_filter.mp hDfilt).1
  have hxD : x ∈ clauseSupport D := (mem_filter.mp hDfilt).2
  have hNot := hmin.2 D hDG
  have hEx : ∃ a, cnfSat a (G.erase D) ∧ ¬ clauseSat a C := by
    have hsub : G.erase D ⊆ F := (erase_subset D G).trans hmin.1.1
    by_contra hnone
    push Not at hnone
    exact hNot ⟨hsub, hnone⟩
  obtain ⟨a, haErase, haC⟩ := hEx
  have haDfalse : ¬ clauseSat a D := by
    intro hDsat
    have haG : cnfSat a G := by
      intro E hE
      by_cases hED : E = D
      · simpa [hED] using hDsat
      · exact haErase E (mem_erase.mpr ⟨hED, hE⟩)
    exact haC (hmin.1.2 a haG)
  obtain ⟨l, hlD, rfl⟩ := mem_image.mp hxD
  have haLit : a l.var = !l.pos := by
    have hNotLit : ¬ litSat a l := fun hlit => haDfalse ⟨l, hlD, hlit⟩
    simp only [litSat] at hNotLit
    cases hpos : l.pos <;> cases ha' : a l.var <;> simp_all
  set a' := csFlipVar a l.var
  have ha'D : clauseSat a' D := by
    refine ⟨l, hlD, ?_⟩
    simp [litSat, a', csFlipVar, haLit]
  have hxOther : ∀ E ∈ G.erase D, l.var ∉ clauseSupport E := by
    intro E hE hxE
    have hEfilt : E ∈ G.filter (fun E => l.var ∈ clauseSupport E) :=
      mem_filter.mpr ⟨(mem_erase.mp hE).2, hxE⟩
    have hEq : E = D := by
      have hsing : G.filter (fun E => l.var ∈ clauseSupport E) = {D} := hDsing
      simpa [hsing] using hEfilt
    exact (mem_erase.mp hE).1 hEq
  have ha'Erase : cnfSat a' (G.erase D) :=
    (cnfSat_csFlipVar_of_not_mem_supports a (G.erase D) l.var hxOther).2 haErase
  have ha'C : ¬ clauseSat a' C := by
    simpa [a', clauseSat_csFlipVar_of_not_mem a C l.var hxC] using haC
  have ha'G : cnfSat a' G := by
    intro E hE
    by_cases hED : E = D
    · simpa [hED] using ha'D
    · exact ha'Erase E (mem_erase.mpr ⟨hED, hE⟩)
  exact ha'C (hmin.1.2 a' ha'G)

/-- Boundary size is at most clause width under erase-minimal axiom complexes. -/
theorem clauseSetBoundary_card_le_clause_card {F : CNF} {G : Finset Clause}
    {C : Clause} (hmin : IsEraseMinimalClauseComplex F G C) :
    (clauseSetBoundary G).card ≤ C.card := by
  have hsub := clauseSetBoundary_subset_clauseVars hmin
  exact (card_le_card hsub).trans card_image_le

/-- Singleton axiom set implies its clause. -/
theorem csClauseImplies_hyp {F : CNF} {C : Clause} (hC : C ∈ F) :
    csClauseImplies F ({C} : Finset Clause) C :=
  ⟨singleton_subset_iff.mpr hC, fun a ha => ha C (mem_singleton_self _)⟩

/-- Erase-minimal singleton when `C` is falsifiable (non-tautology). -/
theorem isEraseMinimalClauseComplex_hyp {F : CNF} {C : Clause}
    (hC : C ∈ F) (hFals : ∃ a, ¬ clauseSat a C) :
    IsEraseMinimalClauseComplex F ({C} : Finset Clause) C := by
  refine ⟨csClauseImplies_hyp hC, ?_⟩
  intro D hD himp
  have hDeq : D = C := mem_singleton.mp hD
  have hempty : ({C} : Finset Clause).erase D = ∅ := by simp [hDeq]
  have himp' : csClauseImplies F (∅ : Finset Clause) C := by
    simpa [hempty] using himp
  obtain ⟨a, ha⟩ := hFals
  exact ha (himp'.2 a (by intro E hE; simp at hE))

/-- Implication preserved by resolution on the union of axiom sets. -/
theorem csClauseImplies_resolvent {F : CNF} {C D : Clause} (x : ℕ)
    {G H : Finset Clause}
    (hC : csClauseImplies F G C) (hD : csClauseImplies F H D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    csClauseImplies F (G ∪ H) (resolvent C D x) := by
  refine ⟨union_subset hC.1 hD.1, fun a ha => ?_⟩
  have hCs : clauseSat a C := hC.2 a (fun E hE => ha E (mem_union_left H hE))
  have hDs : clauseSat a D := hD.2 a (fun E hE => ha E (mem_union_right G hE))
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

/-! ## Derivation-indexed clause-set complexes (μ) -/

structure Derivation.CSClauseComplexData {F : CNF} {C : Clause}
    (d : Derivation F C) where
  G : Finset Clause
  isMinimal : IsEraseMinimalClauseComplex F G C

/-- Critical axiom set: erase-minimal μ-complex inside parent union. -/
noncomputable def Derivation.csClauseComplexData {F : CNF} :
    {C : Clause} → (d : Derivation F C) → Derivation.CSClauseComplexData d
  | C, .hyp _ hC =>
    ⟨chooseEraseMinimalClauseComplex ({C} : Finset Clause) (csClauseImplies_hyp hC),
      chooseEraseMinimalClauseComplex_isMinimal ({C} : Finset Clause)
        (csClauseImplies_hyp hC)⟩
  | _, .res x dC dD hx hnx =>
    let pC := dC.csClauseComplexData
    let pD := dD.csClauseComplexData
    let hU := csClauseImplies_resolvent x pC.isMinimal.1 pD.isMinimal.1 hx hnx
    ⟨chooseEraseMinimalClauseComplex (pC.G ∪ pD.G) hU,
      chooseEraseMinimalClauseComplex_isMinimal (pC.G ∪ pD.G) hU⟩

noncomputable def Derivation.csClauseComplex {F : CNF} {C : Clause}
    (d : Derivation F C) : Finset Clause :=
  d.csClauseComplexData.G

theorem csClauseComplex_isMinimal {F : CNF} {C : Clause} (d : Derivation F C) :
    IsEraseMinimalClauseComplex F d.csClauseComplex C :=
  d.csClauseComplexData.isMinimal

theorem csClauseComplex_implies {F : CNF} {C : Clause} (d : Derivation F C) :
    csClauseImplies F d.csClauseComplex C :=
  (csClauseComplex_isMinimal d).1

theorem csClauseComplex_subset_F {F : CNF} {C : Clause} (d : Derivation F C) :
    d.csClauseComplex ⊆ F :=
  (csClauseComplex_implies d).1

theorem csClauseComplex_res_subset {F : CNF} {C D : Clause} (x : ℕ)
    (dC : Derivation F C) (dD : Derivation F D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    (Derivation.res x dC dD hx hnx).csClauseComplex ⊆
      dC.csClauseComplex ∪ dD.csClauseComplex := by
  have hU := csClauseImplies_resolvent x dC.csClauseComplexData.isMinimal.1
    dD.csClauseComplexData.isMinimal.1 hx hnx
  simp only [Derivation.csClauseComplex, Derivation.csClauseComplexData]
  exact chooseEraseMinimalClauseComplex_subset (dC.csClauseComplexData.G ∪
    dD.csClauseComplexData.G) hU

theorem csClauseComplex_hyp_card_le_one {F : CNF} {C : Clause} (hC : C ∈ F) :
    (Derivation.hyp (F := F) C hC).csClauseComplex.card ≤ 1 := by
  have hsub :=
    chooseEraseMinimalClauseComplex_subset ({C} : Finset Clause) (csClauseImplies_hyp hC)
  have hle := card_le_card hsub
  simpa [Derivation.csClauseComplex, Derivation.csClauseComplexData, card_singleton] using hle

/-- Conclusion clause card is at most derivation width. -/
theorem Derivation.cs_concl_card_le_width {F : CNF} {C : Clause}
    (d : Derivation F C) : C.card ≤ d.width := by
  induction d with
  | hyp _ _ => simp [Derivation.width]
  | res _ dC dD _ _ ihC ihD =>
    simp only [Derivation.width, Derivation.conclusion]
    exact le_max_right _ _

/-- Every derived line is BSW-covered: `|∂G| ≤ width(C)`. -/
theorem cs_clause_complex_boundary_le_width {F : CNF} {C : Clause}
    (d : Derivation F C) :
    (clauseSetBoundary d.csClauseComplex).card ≤ d.width := by
  have hbd :=
    clauseSetBoundary_card_le_clause_card (csClauseComplex_isMinimal d)
  exact hbd.trans d.cs_concl_card_le_width

/-- Medium floor for axiom-set complexes, parallel to `tseitinMediumFloor`. -/
def csClauseMediumFloor (m : ℕ) : ℕ := (m / 2 + 2) / 2

private theorem max_ge_csClauseMediumFloor_of_sum_gt_div2 (a b m : ℕ)
    (hsum : m / 2 < a + b) : csClauseMediumFloor m ≤ max a b := by
  have hab : m / 2 + 1 ≤ a + b := Nat.succ_le_of_lt hsum
  have hceil : (a + b + 1) / 2 ≤ max a b := by
    have h2 : a + b ≤ 2 * max a b := by
      cases le_total a b with
      | inl hab =>
        have : max a b = b := max_eq_right hab
        simp [this]; omega
      | inr hba =>
        have : max a b = a := max_eq_left hba
        simp [this]; omega
    omega
  have hfl : csClauseMediumFloor m ≤ (a + b + 1) / 2 := by
    simp only [csClauseMediumFloor]
    omega
  exact hfl.trans hceil

/-- From a derivation whose μ-complex exceeds `m / 2`, extract a medium line. -/
theorem exists_medium_cs_clause_complex_of_large {F : CNF} {C : Clause}
    (π : Derivation F C) (hm : 2 ≤ F.card)
    (hLarge : F.card / 2 < π.csClauseComplex.card) :
    ∃ (C' : Clause) (dC : Derivation F C'),
      dC.csClauseComplex.card ≤ F.card / 2 ∧
        csClauseMediumFloor F.card ≤ dC.csClauseComplex.card ∧
          dC.width ≤ π.width ∧
            (clauseSetBoundary dC.csClauseComplex).card ≤ dC.width := by
  induction π with
  | hyp _ hC =>
    have hle := csClauseComplex_hyp_card_le_one hC
    omega
  | res x dC dD hx hnx ihC ihD =>
    have hsub := csClauseComplex_res_subset x dC dD hx hnx
    have hle : (Derivation.res x dC dD hx hnx).csClauseComplex.card ≤
        (dC.csClauseComplex ∪ dD.csClauseComplex).card := card_le_card hsub
    set SC := dC.csClauseComplex
    set SD := dD.csClauseComplex
    have hUnion : F.card / 2 < (SC ∪ SD).card := lt_of_lt_of_le hLarge hle
    by_cases hCbig : F.card / 2 < SC.card
    · obtain ⟨C', d', h1, h2, h3, h4⟩ := ihC hCbig
      refine ⟨C', d', h1, h2, h3.trans ?_, h4⟩
      simp only [Derivation.width]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · by_cases hDbig : F.card / 2 < SD.card
      · obtain ⟨C', d', h1, h2, h3, h4⟩ := ihD hDbig
        refine ⟨C', d', h1, h2, h3.trans ?_, h4⟩
        simp only [Derivation.width]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · have hCbig' : SC.card ≤ F.card / 2 := Nat.le_of_not_gt hCbig
        have hDbig' : SD.card ≤ F.card / 2 := Nat.le_of_not_gt hDbig
        have hleUnion : (SC ∪ SD).card ≤ SC.card + SD.card := card_union_le SC SD
        have hsum : F.card / 2 < SC.card + SD.card := lt_of_lt_of_le hUnion hleUnion
        have hmax : csClauseMediumFloor F.card ≤ max SC.card SD.card :=
          max_ge_csClauseMediumFloor_of_sum_gt_div2 _ _ _ hsum
        by_cases hSC : SD.card ≤ SC.card
        · have hmed : csClauseMediumFloor F.card ≤ SC.card := by
            simpa [max_eq_left hSC] using hmax
          refine ⟨dC.conclusion, dC, hCbig', hmed, ?_,
            cs_clause_complex_boundary_le_width dC⟩
          exact (le_max_left dC.width dD.width).trans (le_max_left _ _)
        · have hSDle : SC.card ≤ SD.card := le_of_not_ge hSC
          have hmed : csClauseMediumFloor F.card ≤ SD.card := by
            simpa [max_eq_right hSDle] using hmax
          refine ⟨dD.conclusion, dD, hDbig', hmed, ?_,
            cs_clause_complex_boundary_le_width dD⟩
          exact (le_max_right dC.width dD.width).trans (le_max_left _ _)

/-! ## Matchability and clause-set expansion (BSW width machine)

The Ben-Sasson and Wigderson random k-CNF argument uses (i) matchability of
small axiom sets and (ii) boundary expansion of medium axiom sets under
`clauseSetBoundary`. This is the packaging that pairs with the certified
coverage lemma; the pin's variable-side `HasCSExpansion` remains a separate
Frontier reduction target. -/

/-- Every axiom subset of size at most `r` is satisfiable. -/
def IsCSMatchable (F : CNF) (r : ℕ) : Prop :=
  ∀ G : Finset Clause, G ⊆ F → G.card ≤ r → Satisfiable G

/-- Medium axiom sets expand under the clause-set boundary. -/
def HasCSClauseExpansion (F : CNF) (r α : ℕ) : Prop :=
  ∀ G : Finset Clause, G ⊆ F →
    r / 2 ≤ G.card → G.card ≤ r →
      α * G.card ≤ (clauseSetBoundary G).card

/-- Width floor from matchability scale `r` and expansion factor `α`. -/
def csClauseWidthFloor (r α : ℕ) : ℕ := α * (r / 2)

/-- Unsatisfiable CNFs imply every clause from the full axiom set. -/
theorem csClauseImplies_of_unsat {F : CNF} (h : ¬ Satisfiable F) (C : Clause) :
    csClauseImplies F F C :=
  ⟨subset_rfl, fun a ha => False.elim (h ⟨a, ha⟩)⟩

/-- Matchability forces every empty-clause μ-complex above `r`. -/
theorem csClauseComplex_card_gt_of_matchable {F : CNF} {r : ℕ}
    (d : Derivation F (∅ : Clause)) (hMatch : IsCSMatchable F r) :
    r < d.csClauseComplex.card := by
  by_contra hle
  have hsub := csClauseComplex_subset_F d
  obtain ⟨a, ha⟩ := hMatch d.csClauseComplex hsub (le_of_not_gt hle)
  exact not_clauseSat_empty_cs a ((csClauseComplex_implies d).2 a ha)

private theorem max_ge_ceil_half_of_sum_gt (a b t : ℕ)
    (hsum : t < a + b) : (t + 1) / 2 ≤ max a b := by
  have h2 : a + b ≤ 2 * max a b := by
    cases le_total a b with
    | inl hab =>
      have : max a b = b := max_eq_right hab
      simp [this]; omega
    | inr hba =>
      have : max a b = a := max_eq_left hba
      simp [this]; omega
  omega

/-- Extract a medium μ-line when the complex exceeds threshold `t`. -/
theorem exists_medium_cs_clause_complex_thresh {F : CNF} {C : Clause} {t : ℕ}
    (π : Derivation F C) (ht : 1 ≤ t)
    (hLarge : t < π.csClauseComplex.card) :
    ∃ (C' : Clause) (dC : Derivation F C'),
      dC.csClauseComplex.card ≤ t ∧
        (t + 1) / 2 ≤ dC.csClauseComplex.card ∧
          dC.width ≤ π.width ∧
            (clauseSetBoundary dC.csClauseComplex).card ≤ dC.width := by
  induction π with
  | hyp _ hC =>
    have hle := csClauseComplex_hyp_card_le_one hC
    omega
  | res x dC dD hx hnx ihC ihD =>
    have hsub := csClauseComplex_res_subset x dC dD hx hnx
    have hle : (Derivation.res x dC dD hx hnx).csClauseComplex.card ≤
        (dC.csClauseComplex ∪ dD.csClauseComplex).card := card_le_card hsub
    set SC := dC.csClauseComplex
    set SD := dD.csClauseComplex
    have hUnion : t < (SC ∪ SD).card := lt_of_lt_of_le hLarge hle
    by_cases hCbig : t < SC.card
    · obtain ⟨C', d', h1, h2, h3, h4⟩ := ihC hCbig
      refine ⟨C', d', h1, h2, h3.trans ?_, h4⟩
      simp only [Derivation.width]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · by_cases hDbig : t < SD.card
      · obtain ⟨C', d', h1, h2, h3, h4⟩ := ihD hDbig
        refine ⟨C', d', h1, h2, h3.trans ?_, h4⟩
        simp only [Derivation.width]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · have hCbig' : SC.card ≤ t := Nat.le_of_not_gt hCbig
        have hDbig' : SD.card ≤ t := Nat.le_of_not_gt hDbig
        have hleUnion : (SC ∪ SD).card ≤ SC.card + SD.card := card_union_le SC SD
        have hsum : t < SC.card + SD.card := lt_of_lt_of_le hUnion hleUnion
        have hmax : (t + 1) / 2 ≤ max SC.card SD.card :=
          max_ge_ceil_half_of_sum_gt _ _ _ hsum
        by_cases hSC : SD.card ≤ SC.card
        · have hmed : (t + 1) / 2 ≤ SC.card := by
            simpa [max_eq_left hSC] using hmax
          refine ⟨dC.conclusion, dC, hCbig', hmed, ?_,
            cs_clause_complex_boundary_le_width dC⟩
          exact (le_max_left dC.width dD.width).trans (le_max_left _ _)
        · have hSDle : SC.card ≤ SD.card := le_of_not_ge hSC
          have hmed : (t + 1) / 2 ≤ SD.card := by
            simpa [max_eq_right hSDle] using hmax
          refine ⟨dD.conclusion, dD, hDbig', hmed, ?_,
            cs_clause_complex_boundary_le_width dD⟩
          exact (le_max_right dC.width dD.width).trans (le_max_left _ _)

/-- BSW width lower bound under matchability and clause-set expansion. -/
theorem cs_clause_expansion_width_lower_bound {F : CNF} {r α : ℕ}
    (hMatch : IsCSMatchable F r) (hExp : HasCSClauseExpansion F r α)
    (hr : 2 ≤ r) (d : Derivation F (∅ : Clause)) :
    csClauseWidthFloor r α ≤ d.width := by
  have hLarge : r < d.csClauseComplex.card :=
    csClauseComplex_card_gt_of_matchable d hMatch
  have ht : 1 ≤ r := by omega
  obtain ⟨C, dC, hUpper, hLower, hWle, hBd⟩ :=
    exists_medium_cs_clause_complex_thresh d ht hLarge
  have hGsub := csClauseComplex_subset_F dC
  have hGe : r / 2 ≤ dC.csClauseComplex.card := by
    have hhalf : r / 2 ≤ (r + 1) / 2 := by omega
    exact hhalf.trans hLower
  have hExp' := hExp dC.csClauseComplex hGsub hGe hUpper
  have hαle : α * dC.csClauseComplex.card ≤ d.width :=
    (hExp'.trans hBd).trans hWle
  have hfloor : csClauseWidthFloor r α ≤ α * dC.csClauseComplex.card := by
    simp only [csClauseWidthFloor]
    exact Nat.mul_le_mul_left α hGe
  exact hfloor.trans hαle

/-- Size corollary via BSW once the clause-set width floor is available. -/
theorem cs_clause_expansion_size_lower_bound {F : CNF} {r α : ℕ}
    (hMatch : IsCSMatchable F r) (hExp : HasCSClauseExpansion F r α)
    (hr : 2 ≤ r) (d : Derivation F (∅ : Clause)) :
    let W := csClauseWidthFloor r α
    2 ^ ((W - cnfWidth F) * (W - cnfWidth F) /
          (bswRateConst * (cnfVars F).card)) ≤ d.size := by
  intro W
  exact bsw_size_lower_bound F W
    (fun d' => cs_clause_expansion_width_lower_bound hMatch hExp hr d') d

/-! ## Minimal unsatisfiability (matchability infrastructure)

Matchability of scale `r = |F| - 1` is immediate from minimal unsatisfiability:
every proper subset of a minimally unsat CNF is satisfiable. This shrinks the
existence gap without claiming probabilistic expansion. -/

/-- `F` is unsatisfiable, and deleting any single clause restores satisfiability. -/
def IsMinimallyUnsat (F : CNF) : Prop :=
  ¬ Satisfiable F ∧ ∀ C ∈ F, Satisfiable (F.erase C)

/-- Empty CNF is satisfiable (vacuous conjunction). -/
theorem Satisfiable_empty : Satisfiable (∅ : CNF) :=
  ⟨fun _ => true, fun C hC => by cases hC⟩

/-- Satisfiability is downward closed under axiom deletion (subset). -/
theorem Satisfiable.mono_subset {F G : CNF} (hFG : F ⊆ G) (h : Satisfiable G) :
    Satisfiable F := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun C hC => ha C (hFG hC)⟩

/-- Projection of minimal unsatisfiability. -/
theorem IsMinimallyUnsat.not_satisfiable {F : CNF} (h : IsMinimallyUnsat F) :
    ¬ Satisfiable F :=
  h.1

/-- Singleton empty clause is the smallest minimally unsatisfiable CNF. -/
theorem isMinimallyUnsat_singleton_empty :
    IsMinimallyUnsat ({(∅ : Clause)} : CNF) := by
  refine ⟨?_, ?_⟩
  · -- Empty clause is never satisfied.
    rintro ⟨a, ha⟩
    exact not_clauseSat_empty_cs a (ha (∅ : Clause) (mem_singleton_self _))
  · intro C hC
    have hCeq : C = (∅ : Clause) := mem_singleton.mp hC
    simpa [hCeq] using Satisfiable_empty

/-- Matchability is monotone in the scale parameter. -/
theorem IsCSMatchable.mono {F : CNF} {r r' : ℕ}
    (h : IsCSMatchable F r) (hle : r' ≤ r) : IsCSMatchable F r' :=
  fun G hG hcard => h G hG (hcard.trans hle)

/-- Floor at expansion factor one is half the matchability scale. -/
theorem csClauseWidthFloor_one (r : ℕ) : csClauseWidthFloor r 1 = r / 2 := by
  simp [csClauseWidthFloor]

/-- Vacuous clause-set expansion at α = 0. -/
theorem HasCSClauseExpansion.alpha_zero (F : CNF) (r : ℕ) :
    HasCSClauseExpansion F r 0 :=
  fun _G _hG _hlo _hhi => by simp

/-- Singleton axiom sets have boundary equal to the clause support. -/
theorem clauseSetBoundary_singleton (C : Clause) :
    clauseSetBoundary ({C} : Finset Clause) = clauseSupport C := by
  ext x
  constructor
  · intro hx
    have hx' := (mem_clauseSetBoundary_iff _ x).mp hx
    obtain ⟨D, hD, hxD⟩ := mem_biUnion.mp hx'.1
    have hDeq : D = C := mem_singleton.mp hD
    simpa [hDeq] using hxD
  · intro hx
    refine (mem_clauseSetBoundary_iff _ x).mpr ⟨?_, ?_⟩
    · exact mem_biUnion.mpr ⟨C, mem_singleton_self _, hx⟩
    · -- Unique owner is C itself.
      have hfilt : ({C} : Finset Clause).filter (fun D => x ∈ clauseSupport D) = {C} := by
        ext D
        constructor
        · intro hD
          have hDsing : D = C := mem_singleton.mp (mem_filter.mp hD).1
          exact mem_singleton.mpr hDsing
        · intro hD
          have hDeq : D = C := mem_singleton.mp hD
          exact mem_filter.mpr ⟨mem_singleton.mpr hDeq, by simpa [hDeq] using hx⟩
      simp [hfilt]

/-- Minimally unsat CNFs are matchable at scale `|F| - 1`. -/
theorem isCSMatchable_of_minimallyUnsat {F : CNF}
    (h : IsMinimallyUnsat F) : IsCSMatchable F (F.card - 1) := by
  intro G hG hcard
  -- Unsatisfiable CNFs are nonempty (empty is satisfiable).
  have hFne : F.Nonempty := by
    by_contra hempty
    have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    exact h.1 (hFempty ▸ Satisfiable_empty)
  have hpos : 0 < F.card := card_pos.mpr hFne
  -- Scale bound forces a proper subset.
  have hne : G ≠ F := by
    intro heq
    have : F.card ≤ F.card - 1 := by simpa [heq] using hcard
    omega
  have hss : G ⊂ F := (ssubset_iff_subset_ne).2 ⟨hG, hne⟩
  obtain ⟨C, hCmem⟩ := exists_of_ssubset hss
  have hCin : C ∈ F := hCmem.1
  have hCnG : C ∉ G := hCmem.2
  have hGerase : G ⊆ F.erase C := by
    intro D hD
    exact mem_erase.mpr ⟨fun hDeq => hCnG (hDeq ▸ hD), hG hD⟩
  exact Satisfiable.mono_subset hGerase (h.2 C hCin)

/-- Every unsatisfiable CNF has a minimally unsatisfiable axiom subset. -/
theorem exists_minimallyUnsat_subset {F : CNF} (h : ¬ Satisfiable F) :
    ∃ G ⊆ F, IsMinimallyUnsat G := by
  classical
  revert h
  refine Finset.strongInductionOn F ?_
  intro F IH hunsat
  by_cases hmin : ∀ C ∈ F, Satisfiable (F.erase C)
  · exact ⟨F, subset_rfl, hunsat, hmin⟩
  · simp only [not_forall, Classical.not_imp] at hmin
    obtain ⟨C, hC, hCerase⟩ := hmin
    obtain ⟨G, hGsub, hGmin⟩ := IH (F.erase C) (erase_ssubset hC) hCerase
    exact ⟨G, hGsub.trans (erase_subset C F), hGmin⟩

/-- Matchability scale from any unsat CNF via a minimally unsat subset. -/
theorem exists_matchable_subset_of_unsat {F : CNF} (h : ¬ Satisfiable F) :
    ∃ G ⊆ F, IsCSMatchable G (G.card - 1) ∧ ¬ Satisfiable G := by
  obtain ⟨G, hGsub, hGmin⟩ := exists_minimallyUnsat_subset h
  exact ⟨G, hGsub, isCSMatchable_of_minimallyUnsat hGmin, hGmin.not_satisfiable⟩

/-! ## Clause-set expansion via union spreading

Ben-Sasson and Wigderson reduce medium clause-set expansion (`HasCSClauseExpansion`
at α = 1 for 3-CNF) to a union growth (spreading) hypothesis: every medium axiom
set covers at least two distinct variables per clause. The combinatorial core is
the incidence identity `|∂G| + ∑|supp C| ≥ 2|⋃ supp|`, which yields
`|∂G| ≥ |G|` once `∑|supp C| ≤ 3|G|` and `|⋃ supp| ≥ 2|G|`. -/

/-- Occurrence count of a variable inside an axiom set. -/
def clauseOcc (G : Finset Clause) (x : ℕ) : ℕ :=
  (G.filter fun C => x ∈ clauseSupport C).card

/-- Double count pairs `(C, x)` with `x ∈ clauseSupport C`. -/
theorem sum_clauseSupport_card_eq_sum_occ (G : Finset Clause) :
    G.sum (fun C => (clauseSupport C).card) =
      (G.biUnion clauseSupport).sum (fun x => clauseOcc G x) := by
  classical
  let U := G.biUnion clauseSupport
  have hsub : ∀ C ∈ G, clauseSupport C ⊆ U := fun C hC =>
    subset_biUnion_of_mem clauseSupport hC
  have hleft :
      G.sum (fun C => (clauseSupport C).card) =
        G.sum fun C => ∑ x ∈ U, (if x ∈ clauseSupport C then (1 : ℕ) else 0) := by
    refine sum_congr rfl ?_
    intro C hC
    have hfilter : U.filter (fun x => x ∈ clauseSupport C) = clauseSupport C := by
      ext x
      exact ⟨fun hx => (mem_filter.mp hx).2,
        fun hx => mem_filter.mpr ⟨hsub C hC hx, hx⟩⟩
    rw [← sum_filter (p := fun x => x ∈ clauseSupport C) (f := fun _ => (1 : ℕ)),
      hfilter]
    simp
  have hswap :
      G.sum (fun C => ∑ x ∈ U, (if x ∈ clauseSupport C then (1 : ℕ) else 0)) =
        U.sum fun x => G.sum fun C => (if x ∈ clauseSupport C then (1 : ℕ) else 0) :=
    sum_comm
  have hright :
      U.sum (fun x => G.sum fun C => (if x ∈ clauseSupport C then (1 : ℕ) else 0)) =
        U.sum fun x => clauseOcc G x := by
    refine sum_congr rfl ?_
    intro x _
    have h1 :
        G.sum (fun C => (if x ∈ clauseSupport C then (1 : ℕ) else 0)) =
          (G.filter fun C => x ∈ clauseSupport C).sum fun _ => (1 : ℕ) :=
      (sum_filter (p := fun C => x ∈ clauseSupport C) (f := fun _ => (1 : ℕ))).symm
    simpa [clauseOcc, sum_const, nsmul_eq_mul] using h1
  rw [hleft, hswap, hright]

/-- Incidence core: boundary size plus total support mass is at least twice the
union. Equality holds when every non-boundary variable has occurrence exactly two. -/
theorem clauseSetBoundary_card_add_sum_ge (G : Finset Clause) :
    (clauseSetBoundary G).card + G.sum (fun C => (clauseSupport C).card) ≥
      2 * (G.biUnion clauseSupport).card := by
  classical
  set U := G.biUnion clauseSupport
  set B := clauseSetBoundary G
  have hBsub : B ⊆ U := by
    intro x hx
    exact ((mem_clauseSetBoundary_iff G x).mp hx).1
  have hsum := sum_clauseSupport_card_eq_sum_occ G
  -- Pointwise: boundary vars contribute ≥1, non-boundary vars in U contribute ≥2.
  have hle : ∀ x ∈ U, (if x ∈ B then 1 else 2) ≤ clauseOcc G x := by
    intro x hxU
    by_cases hxB : x ∈ B
    · have hocc : clauseOcc G x = 1 := by
        have := (mem_clauseSetBoundary_iff G x).mp hxB
        simpa [clauseOcc] using this.2
      simp [hxB, hocc]
    · simp only [hxB, ite_false]
      have hne : clauseOcc G x ≠ 1 := by
        intro h1
        exact hxB ((mem_clauseSetBoundary_iff G x).mpr
          ⟨hxU, by simpa [clauseOcc] using h1⟩)
      have hpos : 0 < clauseOcc G x := by
        obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hxU
        exact Nat.pos_of_ne_zero fun h0 => by
          have : C ∈ G.filter (fun D => x ∈ clauseSupport D) :=
            mem_filter.mpr ⟨hC, hxC⟩
          have hempty : G.filter (fun D => x ∈ clauseSupport D) = ∅ :=
            card_eq_zero.mp (by simpa [clauseOcc] using h0)
          simp [hempty] at this
      omega
  have hsum_ge :
      U.sum (fun x => if x ∈ B then (1 : ℕ) else 2) ≤
        U.sum (fun x => clauseOcc G x) :=
    sum_le_sum hle
  have hite : B.card + U.sum (fun x => if x ∈ B then (1 : ℕ) else 2) =
      2 * U.card := by
    have hBfilter : U.filter (fun x => x ∈ B) = B := by
      ext x
      exact ⟨fun hx => (mem_filter.mp hx).2,
        fun hx => mem_filter.mpr ⟨hBsub hx, hx⟩⟩
    have h1 :
        U.sum (fun x => if x ∈ B then (1 : ℕ) else 2) =
          (U.filter (fun x => x ∈ B)).sum (fun _ => (1 : ℕ)) +
            (U.filter (fun x => x ∉ B)).sum (fun _ => (2 : ℕ)) := by
      rw [← sum_filter_add_sum_filter_not (s := U) (p := fun x => x ∈ B)]
      refine congrArg₂ _ ?_ ?_
      · refine sum_congr rfl ?_
        intro x hx
        have : x ∈ B := (mem_filter.mp hx).2
        simp [this]
      · refine sum_congr rfl ?_
        intro x hx
        have : x ∉ B := (mem_filter.mp hx).2
        simp [this]
    have h2 :
        (U.filter (fun x => x ∈ B)).sum (fun _ => (1 : ℕ)) = B.card := by
      simp [hBfilter, sum_const]
    have h3 :
        (U.filter (fun x => x ∉ B)).sum (fun _ => (2 : ℕ)) =
          2 * (U.filter (fun x => x ∉ B)).card := by
      simp [sum_const, mul_comm]
    have h4 : (U.filter (fun x => x ∉ B)).card = U.card - B.card := by
      have : U.filter (fun x => x ∉ B) = U \ B := by
        ext x; simp [mem_sdiff]
      rw [this, Finset.card_sdiff, inter_eq_left.mpr hBsub]
    have hlecard : B.card ≤ U.card := card_le_card hBsub
    rw [h1, h2, h3, h4]
    omega
  have hmain :
      B.card + U.sum (fun x => clauseOcc G x) ≥ 2 * U.card := by
    calc
      B.card + U.sum (fun x => clauseOcc G x)
          ≥ B.card + U.sum (fun x => if x ∈ B then (1 : ℕ) else 2) :=
            Nat.add_le_add_left hsum_ge _
      _ = 2 * U.card := hite
  -- Rewrite back through the occurrence identity.
  have : (clauseSetBoundary G).card + G.sum (fun C => (clauseSupport C).card) ≥
      2 * (G.biUnion clauseSupport).card := by
    calc
      (clauseSetBoundary G).card + G.sum (fun C => (clauseSupport C).card)
          = B.card + U.sum (fun x => clauseOcc G x) := by
            simp only [B, U, hsum]
      _ ≥ 2 * U.card := hmain
      _ = 2 * (G.biUnion clauseSupport).card := by simp [U]
  exact this

/-- Weaker α is easier: expansion factors are downward closed. -/
theorem HasCSClauseExpansion.mono_alpha {F : CNF} {r α α' : ℕ}
    (h : HasCSClauseExpansion F r α) (hle : α' ≤ α) :
    HasCSClauseExpansion F r α' :=
  fun G hG hlo hhi =>
    (Nat.mul_le_mul_right G.card hle).trans (h G hG hlo hhi)

/-- Support card never exceeds clause card, hence never exceeds `cnfWidth`. -/
theorem clauseSupport_card_le_cnfWidth {F : CNF} {C : Clause}
    (hC : C ∈ F) : (clauseSupport C).card ≤ cnfWidth F := by
  have hle : C.card ≤ cnfWidth F := Finset.le_sup hC
  exact (card_image_le).trans hle

/-- Total support mass of `G` is at most `k * |G|` when every member has support
size at most `k`. -/
theorem sum_clauseSupport_card_le_mul {G : Finset Clause} {k : ℕ}
    (hw : ∀ C ∈ G, (clauseSupport C).card ≤ k) :
    G.sum (fun C => (clauseSupport C).card) ≤ k * G.card := by
  have h :=
    sum_le_card_nsmul G (fun C => (clauseSupport C).card) k hw
  -- `sum_le_card_nsmul` yields `|G| * k`; commute to `k * |G|`.
  simpa [nsmul_eq_mul, Nat.mul_comm] using h

/-- Medium axiom sets spread: the union of supports grows at rate `γ` per clause. -/
def Spreads (F : CNF) (r γ : ℕ) : Prop :=
  ∀ G : Finset Clause, G ⊆ F →
    r / 2 ≤ G.card → G.card ≤ r →
      γ * G.card ≤ (G.biUnion clauseSupport).card

/-- Spreading at rate 2 plus width at most 3 yields clause-set expansion at α = 1.
This is the exact combinatorial reduction used by the random 3-CNF argument. -/
theorem hasCSClauseExpansion_one_of_spreads_two {F : CNF} {r : ℕ}
    (hw : cnfWidth F ≤ 3) (hsp : Spreads F r 2) :
    HasCSClauseExpansion F r 1 := by
  intro G hG hlo hhi
  have hU : 2 * G.card ≤ (G.biUnion clauseSupport).card := hsp G hG hlo hhi
  have hsum : G.sum (fun C => (clauseSupport C).card) ≤ 3 * G.card := by
    refine sum_clauseSupport_card_le_mul ?_
    intro C hC
    exact (clauseSupport_card_le_cnfWidth (hG hC)).trans hw
  have hcore := clauseSetBoundary_card_add_sum_ge G
  -- `|∂G| + ∑ ≥ 2|U| ≥ 4|G|`, and `∑ ≤ 3|G|`, so `|∂G| ≥ |G|`.
  have h4 : 4 * G.card ≤
      (clauseSetBoundary G).card + G.sum (fun C => (clauseSupport C).card) := by
    have h2U : 4 * G.card ≤ 2 * (G.biUnion clauseSupport).card := by
      -- 2 * (2 * |G|) ≤ 2 * |U|
      have := Nat.mul_le_mul_left 2 hU
      -- this : 2*(2*|G|) ≤ 2*|U|
      convert this using 1 <;> omega
    exact h2U.trans hcore
  have : G.card ≤ (clauseSetBoundary G).card := by omega
  simpa using this

/-- Same reduction under an explicit per-clause support bound (avoids `cnfWidth`). -/
theorem hasCSClauseExpansion_one_of_spreads_two_of_support_le {F : CNF} {r : ℕ}
    (hw : ∀ C ∈ F, (clauseSupport C).card ≤ 3) (hsp : Spreads F r 2) :
    HasCSClauseExpansion F r 1 := by
  intro G hG hlo hhi
  have hU : 2 * G.card ≤ (G.biUnion clauseSupport).card := hsp G hG hlo hhi
  have hsum : G.sum (fun C => (clauseSupport C).card) ≤ 3 * G.card :=
    sum_clauseSupport_card_le_mul fun C hC => hw C (hG hC)
  have hcore := clauseSetBoundary_card_add_sum_ge G
  have h4 : 4 * G.card ≤
      (clauseSetBoundary G).card + G.sum (fun C => (clauseSupport C).card) := by
    have h2U : 4 * G.card ≤ 2 * (G.biUnion clauseSupport).card := by
      have := Nat.mul_le_mul_left 2 hU
      convert this using 1 <;> omega
    exact h2U.trans hcore
  have : G.card ≤ (clauseSetBoundary G).card := by omega
  simpa using this

/-- Vacuous spreading when the medium interval forces the empty set only
(`r ≤ 1` gives floor 0, not informative, but records the API edge). -/
theorem Spreads.alpha_scale_zero (F : CNF) (γ : ℕ) : Spreads F 0 γ := by
  intro G _hG hlo hhi
  have : G.card = 0 := by omega
  simp [this]

/-- Singleton medium sets spread at rate `γ` once every clause support has size
at least `γ`. Useful for tiny-r calibration only. -/
theorem spreads_one_of_support_ge {F : CNF} {γ : ℕ}
    (hge : ∀ C ∈ F, γ ≤ (clauseSupport C).card) : Spreads F 1 γ := by
  intro G hG hlo hhi
  have hcard : G.card = 0 ∨ G.card = 1 := by omega
  cases hcard with
  | inl h0 => simp [h0]
  | inr h1 =>
    obtain ⟨C, rfl⟩ := card_eq_one.mp h1
    have hC : C ∈ F := hG (mem_singleton_self _)
    simpa [biUnion_singleton] using hge C hC

/-! ## Frontier: restated existence plus quarantined variable-side names

Critical path existence is `exists_cs_clause_expanding_3cnf` (clause-set pin).
Sufficient accepted route: produce matchable unsat 3-CNF with `Spreads F (n/4) 2`,
then apply `hasCSClauseExpansion_one_of_spreads_two`. Obsolete variable-side
Frontier theorems remain for archival reference only; do not spend cycles proving
them. -/

namespace CSExpansionFrontier

/-- QUARANTINED (audit 2026-08-09): variable-side coverage is not the BSW lemma.
Accepted coverage is `clauseSetBoundary_subset_clauseVars`. -/
theorem boundaryCovered_of_eraseMinimal {F : CNF} {S : Finset ℕ} {C : Clause}
    (_hmin : IsEraseMinimalCSComplex F S C) :
    boundaryCovered F S C := by
  sorry

/-- QUARANTINED: variable-side width LB under `HasCSExpansion`. Critical path is
`cs_clause_expansion_width_lower_bound` under matchability plus clause-set expansion. -/
theorem cs_expansion_width_lower_bound {F : CNF} {k β α : ℕ}
    (_h : HasCSExpansion F k β α) (_hα : 1 ≤ α) (_hβ : 0 < β)
    (d : Derivation F (∅ : Clause)) :
    csWidthFloor (cnfSupport F).card β α ≤ d.width := by
  sorry

/-- QUARANTINED obsolete existence under variable-side `HasCSExpansion`.
Replaced on the critical path by `exists_cs_clause_expanding_3cnf`. -/
theorem exists_cs_expanding_3cnf :
    ∀ N : ℕ, ∃ (n : ℕ) (F : CNF) (β α : ℕ),
      N ≤ n ∧ (cnfVars F).card = n ∧ β = 4 ∧ α = 1 ∧
        HasCSExpansion F 3 β α ∧ ¬ Satisfiable F ∧
          cnfWidth F < csWidthFloor n β α := by
  sorry

/-- Restated critical-path existence (pin 2026-08-09). Requires matchable,
clause-set expanding, unsatisfiable 3-CNF with informative floor. Sufficient
accepted route: `Spreads F (n/4) 2` plus `hasCSClauseExpansion_one_of_spreads_two`.
Small-n witness search failed; probabilistic spreading remains open (sorry honest). -/
theorem exists_cs_clause_expanding_3cnf :
    ∀ N : ℕ, ∃ (n : ℕ) (F : CNF) (r α : ℕ),
      N ≤ n ∧ (cnfVars F).card = n ∧ cnfWidth F ≤ 3 ∧
        α = 1 ∧ r = n / 4 ∧
          IsCSMatchable F r ∧ HasCSClauseExpansion F r α ∧
            ¬ Satisfiable F ∧ cnfWidth F < csClauseWidthFloor r α := by
  sorry

end CSExpansionFrontier

end SATurday.ProofComplexity
