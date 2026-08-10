import Theory.ProofComplexity.Width
import Theory.ProofComplexity.SizeWidth
import Theory.ProofComplexity.Tseitin

/-!
# Chvatal–Szemeredi expansion for k-CNF (Ladder Rung R2, item 2)

Critical path (pin restated 2026-08-09): `IsCSMatchable`, `HasCSClauseExpansion`,
`csClauseWidthFloor`, certified `cs_clause_expansion_width_lower_bound`.
Existence target: `exists_cs_clause_expanding_3cnf` (Frontier).
Accepted reduction: `Spreads` at rate 2 plus width ≤ 3 yields
`hasCSClauseExpansion_one_of_spreads_two`.
Finite non vacuous inhabitant: `spreadWitnessCNF` with `Spreads _ 2 2`,
matchability at 2, and `hasCSClauseExpansion_spreadWitnessCNF_two`
(packaged as `exists_spreads_two_matchable_unsat_3cnf`; floor not informative).
Informative threshold lemmas: width 3 forces `r ≥ 8` for α = 1 floors;
`spreads_three_of_unions` lifts the pairwise constructor to scale 3.
Single support cubic star encoding: `starCNF` places one clause per vertex;
`spreads_starCNF_of_touching_ge` plus `touching_card_ge_two_of_handshaking_expansion`
package the expander bridge (handshaking identity remains the next obligation);
`SpreadsSupports` packages the probabilistic set system form. Heawood star CNF
is satisfiable and non informative at r = 5.

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

/-! ## Spreads at rate 2 for matchable unsat 3-CNF (finite witness)

Non vacuous scale `r = 2` (medium sets of size 1 and 2). Pairwise support unions
of size at least 4 yield `Spreads F 2 2`, hence `HasCSClauseExpansion F 2 1` via
`hasCSClauseExpansion_one_of_spreads_two`. The concrete witness is an explicit
unsatisfiable width-3 CNF on six variables with pairwise distinct triple supports.
Informative floor (`cnfWidth < csClauseWidthFloor`) fails at this scale and is
not claimed; the `∀ N` Frontier pin remains open. -/

/-- Nonempty clauses are satisfiable as singleton CNFs. -/
theorem Satisfiable.singleton_of_nonempty {C : Clause} (h : C.Nonempty) :
    Satisfiable ({C} : CNF) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨fun x => if x = l.var then l.pos else true, ?_⟩
  intro D hD
  have hDeq : D = C := mem_singleton.mp hD
  subst hDeq
  exact ⟨l, hl, by simp [litSat]⟩

/-- Any two clauses of cardinality at least two are jointly satisfiable. -/
theorem Satisfiable.pair_of_card_ge_two {C D : Clause}
    (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) :
    Satisfiable ({C, D} : CNF) := by
  classical
  by_cases hEq : C = D
  · subst hEq
    have hne : C.Nonempty := card_pos.mp (by omega)
    simpa [pair_eq_singleton] using Satisfiable.singleton_of_nonempty hne
  · obtain ⟨l, hl⟩ := card_pos.mp (show 0 < C.card from by omega)
    let a0 : Assignment := fun x => if x = l.var then l.pos else false
    have hCsat : clauseSat a0 C := ⟨l, hl, by simp [litSat, a0]⟩
    by_cases hDsat : clauseSat a0 D
    · refine ⟨a0, fun E hE => ?_⟩
      rcases mem_insert.mp hE with hE | hE
      · subst hE; exact hCsat
      · have hE' : E = D := mem_singleton.mp hE
        subst hE'; exact hDsat
    · obtain ⟨m, hm⟩ := card_pos.mp (show 0 < D.card from by omega)
      by_cases hvar : m.var = l.var
      · have hrest : (D.erase m).Nonempty := by
          have : (D.erase m).card = D.card - 1 := card_erase_of_mem hm
          exact card_pos.mp (by omega)
        obtain ⟨m', hm'erase⟩ := hrest
        have hm'mem : m' ∈ D := mem_of_mem_erase hm'erase
        have hm'ne : m' ≠ m := (mem_erase.mp hm'erase).1
        have hm'var : m'.var ≠ l.var := by
          intro hv
          by_cases hposEq : m'.pos = l.pos
          · -- Same polarity as `l`: `a0` satisfies `m'`, so satisfies `D`.
            have : litSat a0 m' := by
              simp [litSat, a0, hv, hposEq]
            exact hDsat ⟨m', hm'mem, this⟩
          · -- Opposite polarity: `m'` equals `m` (also opposite of `l` under `a0`).
            have hm_fail : ¬ litSat a0 m := fun h => hDsat ⟨m, hm, h⟩
            have hm_opp : m.pos ≠ l.pos := by
              intro heq
              have : litSat a0 m := by simp [litSat, a0, hvar, heq]
              exact hm_fail this
            have : m' = m := by
              rcases l with ⟨lv, lp⟩
              rcases m with ⟨mv, mb⟩
              rcases m' with ⟨m'v, m'b⟩
              have hv1 : mv = lv := hvar
              have hv2 : m'v = lv := hv
              subst hv1; subst hv2
              cases lp <;> cases mb <;> cases m'b <;> simp_all [Literal]
            exact hm'ne this
        let a1 : Assignment := fun x =>
          if x = l.var then l.pos else if x = m'.var then m'.pos else false
        refine ⟨a1, fun E hE => ?_⟩
        rcases mem_insert.mp hE with hE | hE
        · subst hE; exact ⟨l, hl, by simp [litSat, a1]⟩
        · have : E = D := mem_singleton.mp hE
          subst this
          refine ⟨m', hm'mem, ?_⟩
          simp [litSat, a1, hm'var]
      · let a1 : Assignment := fun x =>
          if x = l.var then l.pos else if x = m.var then m.pos else false
        refine ⟨a1, fun E hE => ?_⟩
        rcases mem_insert.mp hE with hE | hE
        · subst hE; exact ⟨l, hl, by simp [litSat, a1]⟩
        · have : E = D := mem_singleton.mp hE
          subst this
          refine ⟨m, hm, ?_⟩
          simp [litSat, a1, hvar]

/-- Matchability at scale 2 for CNFs whose clauses all have size at least 2. -/
theorem isCSMatchable_two_of_clause_card_ge_two {F : CNF}
    (h : ∀ C ∈ F, 2 ≤ C.card) : IsCSMatchable F 2 := by
  intro G hG hcard
  have hcases : G.card = 0 ∨ G.card = 1 ∨ G.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hGempty : G = ∅ := card_eq_zero.mp h0
    simpa [hGempty] using Satisfiable_empty
  · obtain ⟨C, rfl⟩ := card_eq_one.mp h1
    exact Satisfiable.singleton_of_nonempty
      (card_pos.mp (by have := h C (hG (mem_singleton_self _)); omega))
  · obtain ⟨C, D, hCD, rfl⟩ := card_eq_two.mp h2
    exact Satisfiable.pair_of_card_ge_two
      (h C (hG (mem_insert_self _ _)))
      (h D (hG (mem_insert_of_mem (mem_singleton_self _))))

/-- Distinct size-3 supports force pairwise union size at least 4. -/
theorem clauseSupport_union_card_ge_four_of_ne_triples {C D : Clause}
    (hC : (clauseSupport C).card = 3) (hD : (clauseSupport D).card = 3)
    (hne : clauseSupport C ≠ clauseSupport D) :
    4 ≤ (clauseSupport C ∪ clauseSupport D).card := by
  have hle : (clauseSupport C ∩ clauseSupport D).card ≤ 2 := by
    by_contra hgt
    have hge : 3 ≤ (clauseSupport C ∩ clauseSupport D).card := by omega
    have hsub : clauseSupport C ∩ clauseSupport D ⊆ clauseSupport C :=
      inter_subset_left
    have heq : clauseSupport C ∩ clauseSupport D = clauseSupport C :=
      eq_of_subset_of_card_le hsub (by omega)
    have hCsubD : clauseSupport C ⊆ clauseSupport D := by
      intro x hx
      have hxI : x ∈ clauseSupport C ∩ clauseSupport D := by
        simpa [heq] using hx
      exact (mem_inter.mp hxI).2
    exact hne (eq_of_subset_of_card_le hCsubD (by omega))
  have hcard := card_union_add_card_inter (clauseSupport C) (clauseSupport D)
  omega

/-- Spreading at rate 2 and scale 2 from support lower bounds plus pairwise unions. -/
theorem spreads_two_of_pairwise_union_ge {F : CNF}
    (h1 : ∀ C ∈ F, 2 ≤ (clauseSupport C).card)
    (h2 : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      4 ≤ (clauseSupport C ∪ clauseSupport D).card) :
    Spreads F 2 2 := by
  intro G hG hlo hhi
  have hcases : G.card = 1 ∨ G.card = 2 := by omega
  rcases hcases with h1c | h2c
  · obtain ⟨C, rfl⟩ := card_eq_one.mp h1c
    have : 2 * ({C} : Finset Clause).card ≤ (clauseSupport C).card := by
      simpa using h1 C (hG (mem_singleton_self _))
    simpa [biUnion_singleton] using this
  · obtain ⟨C, D, hCD, rfl⟩ := card_eq_two.mp h2c
    have hC : C ∈ F := hG (mem_insert_self _ _)
    have hD : D ∈ F := hG (mem_insert_of_mem (mem_singleton_self _))
    have hU :
        ({C, D} : Finset Clause).biUnion clauseSupport =
          clauseSupport C ∪ clauseSupport D := by
      ext x; constructor
      · intro hx
        obtain ⟨E, hE, hxE⟩ := mem_biUnion.mp hx
        rcases mem_insert.mp hE with hE | hE
        · subst hE; exact mem_union_left _ hxE
        · have : E = D := mem_singleton.mp hE
          subst this; exact mem_union_right _ hxE
      · intro hx
        rcases mem_union.mp hx with hx | hx
        · exact mem_biUnion.mpr ⟨C, mem_insert_self _ _, hx⟩
        · exact mem_biUnion.mpr
            ⟨D, mem_insert_of_mem (mem_singleton_self _), hx⟩
    have h4 : 4 ≤ (clauseSupport C ∪ clauseSupport D).card := h2 C hC D hD hCD
    have : 2 * ({C, D} : Finset Clause).card ≤
        (({C, D} : Finset Clause).biUnion clauseSupport).card := by
      simpa [hU, card_pair hCD] using h4
    exact this

/-- Assignment read from a finite valuation on `Fin n`. -/
def assignmentOfFin {n : ℕ} (χ : Fin n → Bool) : Assignment :=
  fun v => if h : v < n then χ ⟨v, h⟩ else false

/-- Decidable satisfaction under a total assignment (classical Finset search). -/
instance instDecidableCnfSat (a : Assignment) (F : CNF) :
    Decidable (cnfSat a F) := by
  classical
  unfold cnfSat clauseSat litSat
  infer_instance

/-- Existence of a satisfying valuation on `Fin n` (decidable; honest finite search). -/
def existsSatFin (n : ℕ) (F : CNF) : Prop :=
  ∃ χ : Fin n → Bool, cnfSat (assignmentOfFin χ) F

instance (n : ℕ) (F : CNF) : Decidable (existsSatFin n F) := by
  classical
  unfold existsSatFin
  infer_instance

/-- If all variables of `F` lie below `n` and no `Fin n` valuation satisfies `F`,
then `F` is unsatisfiable. -/
theorem not_satisfiable_of_not_existsSatFin {F : CNF} {n : ℕ}
    (hvars : ∀ v ∈ cnfVars F, v < n)
    (h : ¬ existsSatFin n F) :
    ¬ Satisfiable F := by
  intro ⟨a, ha⟩
  apply h
  refine ⟨fun i => a i.val, ?_⟩
  intro C hC
  obtain ⟨l, hl, hsat⟩ := ha C hC
  refine ⟨l, hl, ?_⟩
  have hv : l.var ∈ cnfVars F :=
    mem_biUnion.mpr ⟨C, hC, mem_image.mpr ⟨l, hl, rfl⟩⟩
  have hlt : l.var < n := hvars _ hv
  simpa [litSat, assignmentOfFin, hlt] using hsat

/-! ### Explicit witness CNF (six variables, fourteen distinct triples) -/

/-- Clause of the spreading witness, indexed for compact packaging. -/
def spreadWitnessClause : Fin 14 → Clause
  | ⟨0, _⟩ => {⟨0, false⟩, ⟨2, true⟩, ⟨5, true⟩}
  | ⟨1, _⟩ => {⟨2, false⟩, ⟨4, false⟩, ⟨5, true⟩}
  | ⟨2, _⟩ => {⟨1, true⟩, ⟨2, false⟩, ⟨5, false⟩}
  | ⟨3, _⟩ => {⟨0, false⟩, ⟨1, false⟩, ⟨4, true⟩}
  | ⟨4, _⟩ => {⟨1, false⟩, ⟨4, true⟩, ⟨5, true⟩}
  | ⟨5, _⟩ => {⟨1, false⟩, ⟨2, true⟩, ⟨3, false⟩}
  | ⟨6, _⟩ => {⟨1, true⟩, ⟨3, false⟩, ⟨4, true⟩}
  | ⟨7, _⟩ => {⟨3, false⟩, ⟨4, true⟩, ⟨5, false⟩}
  | ⟨8, _⟩ => {⟨1, true⟩, ⟨3, true⟩, ⟨5, true⟩}
  | ⟨9, _⟩ => {⟨0, false⟩, ⟨1, true⟩, ⟨3, false⟩}
  | ⟨10, _⟩ => {⟨0, false⟩, ⟨2, true⟩, ⟨3, true⟩}
  | ⟨11, _⟩ => {⟨1, false⟩, ⟨2, false⟩, ⟨4, false⟩}
  | ⟨12, _⟩ => {⟨0, true⟩, ⟨4, true⟩, ⟨5, false⟩}
  | ⟨13, _⟩ => {⟨0, true⟩, ⟨2, true⟩, ⟨4, false⟩}

/-- Matchable unsatisfiable width-3 CNF with `Spreads _ 2 2`. -/
def spreadWitnessCNF : CNF :=
  (Finset.univ : Finset (Fin 14)).image spreadWitnessClause

theorem spreadWitnessClause_card (i : Fin 14) :
    (spreadWitnessClause i).card = 3 := by
  fin_cases i <;> decide

theorem spreadWitnessClause_support_card (i : Fin 14) :
    (clauseSupport (spreadWitnessClause i)).card = 3 := by
  fin_cases i <;> decide

theorem mem_spreadWitnessCNF {C : Clause} :
    C ∈ spreadWitnessCNF ↔ ∃ i : Fin 14, spreadWitnessClause i = C := by
  simp [spreadWitnessCNF, mem_image]

theorem spreadWitnessCNF_clause_card {C : Clause}
    (hC : C ∈ spreadWitnessCNF) : C.card = 3 := by
  obtain ⟨i, rfl⟩ := mem_spreadWitnessCNF.mp hC
  exact spreadWitnessClause_card i

theorem spreadWitnessCNF_support_card {C : Clause}
    (hC : C ∈ spreadWitnessCNF) : (clauseSupport C).card = 3 := by
  obtain ⟨i, rfl⟩ := mem_spreadWitnessCNF.mp hC
  exact spreadWitnessClause_support_card i

theorem spreadWitnessCNF_cnfWidth_le :
    cnfWidth spreadWitnessCNF ≤ 3 :=
  Finset.sup_le fun C hC => (spreadWitnessCNF_clause_card hC).le

theorem spreadWitnessClause_support_injective {i j : Fin 14}
    (h : clauseSupport (spreadWitnessClause i) =
      clauseSupport (spreadWitnessClause j)) :
    i = j := by
  revert h
  fin_cases i <;> fin_cases j <;> decide

theorem spreadWitnessCNF_pairwise_union_ge :
    ∀ C ∈ spreadWitnessCNF, ∀ D ∈ spreadWitnessCNF, C ≠ D →
      4 ≤ (clauseSupport C ∪ clauseSupport D).card := by
  intro C hC D hD hne
  obtain ⟨i, rfl⟩ := mem_spreadWitnessCNF.mp hC
  obtain ⟨j, rfl⟩ := mem_spreadWitnessCNF.mp hD
  have hij : i ≠ j := fun heq => hne (congrArg _ heq)
  have hsup :
      clauseSupport (spreadWitnessClause i) ≠
        clauseSupport (spreadWitnessClause j) :=
    fun heq => hij (spreadWitnessClause_support_injective heq)
  exact clauseSupport_union_card_ge_four_of_ne_triples
    (spreadWitnessClause_support_card i) (spreadWitnessClause_support_card j) hsup

theorem spreads_spreadWitnessCNF_two : Spreads spreadWitnessCNF 2 2 :=
  spreads_two_of_pairwise_union_ge
    (fun C hC => by have := spreadWitnessCNF_support_card hC; omega)
    spreadWitnessCNF_pairwise_union_ge

theorem isCSMatchable_spreadWitnessCNF_two :
    IsCSMatchable spreadWitnessCNF 2 :=
  isCSMatchable_two_of_clause_card_ge_two fun C hC => by
    have := spreadWitnessCNF_clause_card hC; omega

theorem hasCSClauseExpansion_spreadWitnessCNF_two :
    HasCSClauseExpansion spreadWitnessCNF 2 1 :=
  hasCSClauseExpansion_one_of_spreads_two
    spreadWitnessCNF_cnfWidth_le spreads_spreadWitnessCNF_two

theorem spreadWitnessCNF_vars_lt_six {v : ℕ}
    (hv : v ∈ cnfVars spreadWitnessCNF) : v < 6 := by
  simp only [cnfVars, mem_biUnion, mem_spreadWitnessCNF] at hv
  obtain ⟨C, ⟨i, rfl⟩, hvC⟩ := hv
  fin_cases i <;>
    · simp only [spreadWitnessClause, clauseVars, mem_image] at hvC
      aesop

/-- Finite valuation search: no `Fin 6` assignment satisfies the witness. -/
theorem not_existsSatFin_spreadWitnessCNF :
    ¬ existsSatFin 6 spreadWitnessCNF := by
  decide

theorem spreadWitnessCNF_unsat : ¬ Satisfiable spreadWitnessCNF :=
  not_satisfiable_of_not_existsSatFin
    (fun _ hv => spreadWitnessCNF_vars_lt_six hv) not_existsSatFin_spreadWitnessCNF

/-- Packaged finite advance toward `exists_cs_clause_expanding_3cnf`:
matchable unsat width-3 CNF with `Spreads` at rate 2, hence clause-set expansion
at α = 1. Floor informativeness is not claimed at `r = 2`. -/
theorem exists_spreads_two_matchable_unsat_3cnf :
    ∃ (F : CNF) (r : ℕ),
      cnfWidth F ≤ 3 ∧ r = 2 ∧
        IsCSMatchable F r ∧ Spreads F r 2 ∧ HasCSClauseExpansion F r 1 ∧
          ¬ Satisfiable F :=
  ⟨spreadWitnessCNF, 2, spreadWitnessCNF_cnfWidth_le, rfl,
    isCSMatchable_spreadWitnessCNF_two, spreads_spreadWitnessCNF_two,
    hasCSClauseExpansion_spreadWitnessCNF_two, spreadWitnessCNF_unsat⟩

/-! ## Informative floor threshold and medium union Spreads constructors

For width at most 3 and α = 1, `cnfWidth F < csClauseWidthFloor r 1` forces
`r ≥ 8` whenever the formula actually has a width-3 clause. Finite Spreads
witnesses at r = 2 are therefore non informative. The constructors below package
Spreads at general r from explicit medium union lower bounds (the r = 2 case
recovers `spreads_two_of_pairwise_union_ge`). -/

/-- Floor at α = 1 is exactly half the matchability scale. -/
theorem csClauseWidthFloor_alpha_one_lt_iff (r w : ℕ) :
    w < csClauseWidthFloor r 1 ↔ w < r / 2 := by
  simp [csClauseWidthFloor]

/-- If some clause has card at least 3, an informative α = 1 floor needs `r ≥ 8`. -/
theorem informative_cs_floor_requires_r_ge_eight {F : CNF} {r : ℕ}
    (h3 : ∃ C ∈ F, 3 ≤ C.card)
    (hinfo : cnfWidth F < csClauseWidthFloor r 1) : 8 ≤ r := by
  obtain ⟨C, hC, hC3⟩ := h3
  have hw : 3 ≤ cnfWidth F := (le_sup (f := fun D : Clause => D.card) hC).trans' hC3
  have : 3 < r / 2 := lt_of_le_of_lt hw (by simpa [csClauseWidthFloor] using hinfo)
  omega

/-- Same threshold under the common `cnfWidth F = 3` packaging. -/
theorem informative_cs_floor_of_cnfWidth_eq_three {F : CNF} {r : ℕ}
    (hw : cnfWidth F = 3)
    (hinfo : cnfWidth F < csClauseWidthFloor r 1) : 8 ≤ r := by
  have : 3 < r / 2 := by
    simpa [hw, csClauseWidthFloor] using hinfo
  omega

/-- Spreads from a uniform medium union lower bound (definition unfolded). -/
theorem spreads_of_medium_biUnion_ge {F : CNF} {r γ : ℕ}
    (h : ∀ G : Finset Clause, G ⊆ F →
      r / 2 ≤ G.card → G.card ≤ r →
        γ * G.card ≤ (G.biUnion clauseSupport).card) :
    Spreads F r γ :=
  h

/-- Spreading at rate 2 and scale 3 from support lower bounds on medium sizes
1, 2, and 3. -/
theorem spreads_three_of_unions {F : CNF}
    (h1 : ∀ C ∈ F, 2 ≤ (clauseSupport C).card)
    (h2 : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      4 ≤ (clauseSupport C ∪ clauseSupport D).card)
    (h3 : ∀ C ∈ F, ∀ D ∈ F, ∀ E ∈ F,
      C ≠ D → C ≠ E → D ≠ E →
        6 ≤ (clauseSupport C ∪ clauseSupport D ∪ clauseSupport E).card) :
    Spreads F 3 2 := by
  intro G hG hlo hhi
  have hcases : G.card = 1 ∨ G.card = 2 ∨ G.card = 3 := by omega
  rcases hcases with h1c | h2c | h3c
  · obtain ⟨C, rfl⟩ := card_eq_one.mp h1c
    have : 2 * ({C} : Finset Clause).card ≤ (clauseSupport C).card := by
      simpa using h1 C (hG (mem_singleton_self _))
    simpa [biUnion_singleton] using this
  · obtain ⟨C, D, hCD, rfl⟩ := card_eq_two.mp h2c
    have hC : C ∈ F := hG (mem_insert_self _ _)
    have hD : D ∈ F := hG (mem_insert_of_mem (mem_singleton_self _))
    have hU :
        ({C, D} : Finset Clause).biUnion clauseSupport =
          clauseSupport C ∪ clauseSupport D := by
      ext x; constructor
      · intro hx
        obtain ⟨E, hE, hxE⟩ := mem_biUnion.mp hx
        rcases mem_insert.mp hE with hE | hE
        · subst hE; exact mem_union_left _ hxE
        · have : E = D := mem_singleton.mp hE
          subst this; exact mem_union_right _ hxE
      · intro hx
        rcases mem_union.mp hx with hx | hx
        · exact mem_biUnion.mpr ⟨C, mem_insert_self _ _, hx⟩
        · exact mem_biUnion.mpr
            ⟨D, mem_insert_of_mem (mem_singleton_self _), hx⟩
    have h4 : 4 ≤ (clauseSupport C ∪ clauseSupport D).card := h2 C hC D hD hCD
    have : 2 * ({C, D} : Finset Clause).card ≤
        (({C, D} : Finset Clause).biUnion clauseSupport).card := by
      simpa [hU, card_pair hCD] using h4
    exact this
  · obtain ⟨C, D, E, hCD, hCE, hDE, rfl⟩ := card_eq_three.mp h3c
    have hC : C ∈ F := hG (by simp)
    have hD : D ∈ F := hG (by simp)
    have hE : E ∈ F := hG (by simp)
    have hU :
        ({C, D, E} : Finset Clause).biUnion clauseSupport =
          clauseSupport C ∪ clauseSupport D ∪ clauseSupport E := by
      ext x; constructor
      · intro hx
        obtain ⟨K, hK, hxK⟩ := mem_biUnion.mp hx
        have hKmem : K = C ∨ K = D ∨ K = E := by
          simpa [mem_insert, mem_singleton] using hK
        rcases hKmem with rfl | rfl | rfl
        · exact mem_union_left _ (mem_union_left _ hxK)
        · exact mem_union_left _ (mem_union_right _ hxK)
        · exact mem_union_right _ hxK
      · intro hx
        rcases mem_union.mp hx with hx | hx
        · rcases mem_union.mp hx with hx | hx
          · exact mem_biUnion.mpr ⟨C, by simp, hx⟩
          · exact mem_biUnion.mpr ⟨D, by simp, hx⟩
        · exact mem_biUnion.mpr ⟨E, by simp, hx⟩
    have h6 :
        6 ≤ (clauseSupport C ∪ clauseSupport D ∪ clauseSupport E).card :=
      h3 C hC D hD E hE hCD hCE hDE
    have hcard : ({C, D, E} : Finset Clause).card = 3 :=
      (card_eq_three (s := {C, D, E})).mpr ⟨C, D, E, hCD, hCE, hDE, rfl⟩
    have : 2 * ({C, D, E} : Finset Clause).card ≤
        (({C, D, E} : Finset Clause).biUnion clauseSupport).card := by
      simpa [hU, hcard] using h6
    exact this

/-- Non informative calibration: r = 2 yields floor 1, which cannot beat width 3. -/
theorem spreadWitnessCNF_floor_not_informative :
    ¬ cnfWidth spreadWitnessCNF < csClauseWidthFloor 2 1 := by
  intro h
  have hfloor : csClauseWidthFloor 2 1 = 1 := by simp [csClauseWidthFloor]
  rw [hfloor] at h
  set C0 : Clause := spreadWitnessClause ⟨0, by omega⟩
  have hC : C0 ∈ spreadWitnessCNF := mem_spreadWitnessCNF.mpr ⟨⟨0, by omega⟩, rfl⟩
  have hcard : C0.card = 3 := spreadWitnessClause_card ⟨0, by omega⟩
  have hle : C0.card ≤ cnfWidth spreadWitnessCNF := by
    simpa [cnfWidth, C0] using Finset.le_sup (f := Finset.card) hC
  omega

/-! ## Single support cubic star encoding (expander to Spreads scaffolding)

Full `tseitinCNF` repeats supports, so Spreads fails on expanders. The star
encoding places one clause per vertex on incident edge variables. This cluster
certifies the encoding, the support union identity, and Spreads from a medium
touching lower bound. The remaining bridge is handshaking plus expansion:
`2 |edgesTouching S| = 3|S| + |∂S|` turns `HasExpansion _ 1` into that bound.
All positive star CNFs are satisfiable; unsat polarity remains open. -/

/-- Edges with both endpoints in `S`. -/
def edgesInternal {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) :
    Finset (FinEdge n) :=
  G.filter fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S

/-- Edges with at least one endpoint in `S`. -/
def edgesTouching {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) :
    Finset (FinEdge n) :=
  S.biUnion (incident G)

theorem mem_edgesInternal_iff {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} :
    e ∈ edgesInternal G S ↔ e ∈ G ∧ e.val.1 ∈ S ∧ e.val.2 ∈ S := by
  simp [edgesInternal]

theorem mem_edgesTouching_iff {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} :
    e ∈ edgesTouching G S ↔ e ∈ G ∧ (e.val.1 ∈ S ∨ e.val.2 ∈ S) := by
  constructor
  · intro he
    obtain ⟨v, hvS, heInc⟩ := mem_biUnion.mp he
    obtain ⟨heG, hends⟩ := mem_incident_iff.mp heInc
    refine ⟨heG, ?_⟩
    cases hends with
    | inl h => exact Or.inl (h ▸ hvS)
    | inr h => exact Or.inr (h ▸ hvS)
  · rintro ⟨heG, h | h⟩
    · exact mem_biUnion.mpr
        ⟨e.val.1, h, mem_incident_iff.mpr ⟨heG, Or.inl rfl⟩⟩
    · exact mem_biUnion.mpr
        ⟨e.val.2, h, mem_incident_iff.mpr ⟨heG, Or.inr rfl⟩⟩

theorem edgesTouching_eq_internal_union_boundary {n : ℕ}
    (G : FinGraph n) (S : Finset (Fin n)) :
    edgesTouching G S = edgesInternal G S ∪ edgeBoundary G S := by
  ext e
  constructor
  · intro he
    obtain ⟨heG, hS⟩ := (mem_edgesTouching_iff (G := G) (S := S)).mp he
    by_cases h1 : e.val.1 ∈ S
    · by_cases h2 : e.val.2 ∈ S
      · exact mem_union.mpr
          (Or.inl (mem_edgesInternal_iff.mpr ⟨heG, h1, h2⟩))
      · exact mem_union.mpr
          (Or.inr (mem_edgeBoundary_iff.mpr ⟨heG, Or.inl ⟨h1, h2⟩⟩))
    · have h2 : e.val.2 ∈ S := by
        cases hS with
        | inl h => exact (h1 h).elim
        | inr h => exact h
      exact mem_union.mpr
        (Or.inr (mem_edgeBoundary_iff.mpr ⟨heG, Or.inr ⟨h1, h2⟩⟩))
  · intro he
    cases mem_union.mp he with
    | inl heI =>
      obtain ⟨heG, h1, _⟩ := mem_edgesInternal_iff.mp heI
      exact (mem_edgesTouching_iff (G := G) (S := S)).mpr ⟨heG, Or.inl h1⟩
    | inr heB =>
      obtain ⟨heG, hcut⟩ := mem_edgeBoundary_iff.mp heB
      cases hcut with
      | inl h =>
        exact (mem_edgesTouching_iff (G := G) (S := S)).mpr ⟨heG, Or.inl h.1⟩
      | inr h =>
        exact (mem_edgesTouching_iff (G := G) (S := S)).mpr ⟨heG, Or.inr h.2⟩

theorem disjoint_edgesInternal_edgeBoundary {n : ℕ}
    (G : FinGraph n) (S : Finset (Fin n)) :
    Disjoint (edgesInternal G S) (edgeBoundary G S) := by
  refine disjoint_left.mpr ?_
  intro e heI heB
  obtain ⟨_, h1, h2⟩ := mem_edgesInternal_iff.mp heI
  obtain ⟨_, hcut⟩ := mem_edgeBoundary_iff.mp heB
  cases hcut with
  | inl h => exact h.2 h2
  | inr h => exact h.1 h1

/-- One all positive forbidding clause on the star of `v`. -/
def starClause {n : ℕ} (G : FinGraph n) (v : Fin n) : Clause :=
  parityForbidClause (incident G v) (∅ : Finset (FinEdge n))

/-- Single support cubic encoding: one star clause per vertex. -/
def starCNF {n : ℕ} (G : FinGraph n) : CNF :=
  (univ : Finset (Fin n)).image (starClause G)

theorem clauseSupport_starClause {n : ℕ} (G : FinGraph n) (v : Fin n) :
    clauseSupport (starClause G v) = (incident G v).image edgeVar := by
  ext x
  constructor
  · intro hx
    simp only [clauseSupport, starClause, parityForbidClause, clauseVars,
      mem_image] at hx
    obtain ⟨l, ⟨e, he, rfl⟩, rfl⟩ := hx
    exact mem_image.mpr ⟨e, he, rfl⟩
  · intro hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    simp only [clauseSupport, starClause, parityForbidClause, clauseVars,
      mem_image]
    exact ⟨⟨edgeVar e, true⟩, ⟨e, he, rfl⟩, rfl⟩

theorem starClause_card_of_regular3 {n : ℕ} {G : FinGraph n}
    (hreg : IsRegular G 3) (hn : 0 < n) (v : Fin n) :
    (starClause G v).card = 3 := by
  rw [starClause, card_parityForbidClause (incident G v) ∅ hn, ← degree, hreg]

theorem starCNF_cnfWidth_le {n : ℕ} {G : FinGraph n}
    (hreg : IsRegular G 3) (hn : 0 < n) :
    cnfWidth (starCNF G) ≤ 3 := by
  refine Finset.sup_le ?_
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.mp hC
  exact (starClause_card_of_regular3 hreg hn v).le

theorem card_edges_between_le_one {n : ℕ} (G : FinGraph n) {v w : Fin n}
    (hne : v ≠ w) :
    (G.filter fun e =>
        (e.val.1 = v ∧ e.val.2 = w) ∨ (e.val.1 = w ∧ e.val.2 = v)).card ≤ 1 := by
  classical
  by_cases hvw : v < w
  · set e0 : FinEdge n := ⟨(v, w), hvw⟩
    have hsub :
        (G.filter fun e =>
            (e.val.1 = v ∧ e.val.2 = w) ∨
              (e.val.1 = w ∧ e.val.2 = v)) ⊆
          ({e0} : Finset (FinEdge n)) := by
      intro e he
      obtain ⟨_, hpair⟩ := mem_filter.mp he
      cases hpair with
      | inl h => exact mem_singleton.mpr (Subtype.ext (Prod.ext h.1 h.2))
      | inr h =>
        have : w < v := by
          have hlt := e.property
          rw [h.1, h.2] at hlt
          exact hlt
        exact (lt_asymm hvw this).elim
    exact (card_le_card hsub).trans (by simp [e0])
  · have hwv : w < v := lt_of_le_of_ne (le_of_not_gt hvw) (Ne.symm hne)
    set e0 : FinEdge n := ⟨(w, v), hwv⟩
    have hsub :
        (G.filter fun e =>
            (e.val.1 = v ∧ e.val.2 = w) ∨
              (e.val.1 = w ∧ e.val.2 = v)) ⊆
          ({e0} : Finset (FinEdge n)) := by
      intro e he
      obtain ⟨_, hpair⟩ := mem_filter.mp he
      cases hpair with
      | inl h =>
        have : v < w := by
          have hlt := e.property
          rw [h.1, h.2] at hlt
          exact hlt
        exact (lt_asymm hwv this).elim
      | inr h => exact mem_singleton.mpr (Subtype.ext (Prod.ext h.1 h.2))
    exact (card_le_card hsub).trans (by simp [e0])

theorem eq_of_incident_eq_of_regular3 {n : ℕ} {G : FinGraph n}
    (hreg : IsRegular G 3) {v w : Fin n}
    (h : incident G v = incident G w) : v = w := by
  classical
  by_contra hne
  have hall : ∀ e ∈ incident G v, e.val.1 = w ∨ e.val.2 = w := by
    intro e he
    have he' : e ∈ incident G w := by simpa [h] using he
    exact (mem_incident_iff.mp he').2
  have hsub :
      incident G v ⊆
        G.filter fun e =>
          (e.val.1 = v ∧ e.val.2 = w) ∨ (e.val.1 = w ∧ e.val.2 = v) := by
    intro e he
    obtain ⟨heG, hv⟩ := mem_incident_iff.mp he
    have hw := hall e he
    refine mem_filter.mpr ⟨heG, ?_⟩
    cases hv with
    | inl hv1 =>
      cases hw with
      | inl hw1 => exact (hne (hv1.symm.trans hw1)).elim
      | inr hw2 => exact Or.inl ⟨hv1, hw2⟩
    | inr hv2 =>
      cases hw with
      | inl hw1 => exact Or.inr ⟨hw1, hv2⟩
      | inr hw2 => exact (hne (hv2.symm.trans hw2)).elim
  have hle := (card_le_card hsub).trans (card_edges_between_le_one G hne)
  have : (incident G v).card = 3 := hreg v
  omega

theorem starClause_injective_of_regular3 {n : ℕ} {G : FinGraph n}
    (hreg : IsRegular G 3) (hn : 0 < n) {v w : Fin n}
    (h : starClause G v = starClause G w) : v = w := by
  have hsup :
      clauseSupport (starClause G v) = clauseSupport (starClause G w) :=
    congrArg _ h
  have himg :
      (incident G v).image edgeVar = (incident G w).image edgeVar := by
    simpa [clauseSupport_starClause] using hsup
  have hinj := edgeVar_injective n hn
  have hinc : incident G v = incident G w := by
    ext e
    constructor
    · intro he
      have hx : edgeVar e ∈ (incident G v).image edgeVar :=
        mem_image_of_mem _ he
      have hx' : edgeVar e ∈ (incident G w).image edgeVar := by
        simpa [himg] using hx
      obtain ⟨e', he', hv⟩ := mem_image.mp hx'
      exact (hinj hv) ▸ he'
    · intro he
      have hx : edgeVar e ∈ (incident G w).image edgeVar :=
        mem_image_of_mem _ he
      have hx' : edgeVar e ∈ (incident G v).image edgeVar := by
        simpa [himg] using hx
      obtain ⟨e', he', hv⟩ := mem_image.mp hx'
      exact (hinj hv) ▸ he'
  exact eq_of_incident_eq_of_regular3 hreg hinc

theorem exists_vertexSet_of_subset_starCNF {n : ℕ} {G : FinGraph n}
    {H : Finset Clause} (hH : H ⊆ starCNF G) :
    ∃ S : Finset (Fin n), H = S.image (starClause G) := by
  refine ⟨univ.filter fun v => starClause G v ∈ H, ?_⟩
  ext C
  constructor
  · intro hC
    obtain ⟨v, _, rfl⟩ := mem_image.mp (hH hC)
    exact mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hC⟩, rfl⟩
  · intro hC
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hC
    exact (mem_filter.mp hv).2

theorem biUnion_clauseSupport_star_eq {n : ℕ} (G : FinGraph n)
    (S : Finset (Fin n)) :
    (S.image (starClause G)).biUnion clauseSupport =
      (edgesTouching G S).image edgeVar := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hx
    obtain ⟨v, hvS, rfl⟩ := mem_image.mp hC
    have hx' : x ∈ (incident G v).image edgeVar := by
      simpa [clauseSupport_starClause] using hxC
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx'
    exact mem_image.mpr ⟨e, mem_biUnion.mpr ⟨v, hvS, he⟩, rfl⟩
  · intro hx
    obtain ⟨e, heT, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hvS, he⟩ := mem_biUnion.mp heT
    refine mem_biUnion.mpr ⟨starClause G v, mem_image_of_mem _ hvS, ?_⟩
    simpa [clauseSupport_starClause] using mem_image_of_mem edgeVar he

/-- Spreads for `starCNF` from a medium touching lower bound (rate 2).
 paired with handshaking plus `HasExpansion _ 1` this yields the expander bridge. -/
theorem spreads_starCNF_of_touching_ge {n : ℕ} {G : FinGraph n} {r : ℕ}
    (hreg : IsRegular G 3) (hn : 0 < n)
    (htouch : ∀ S : Finset (Fin n),
      r / 2 ≤ S.card → S.card ≤ r →
        2 * S.card ≤ (edgesTouching G S).card) :
    Spreads (starCNF G) r 2 := by
  intro H hH hlo hhi
  obtain ⟨S, rfl⟩ := exists_vertexSet_of_subset_starCNF hH
  have hinj : Set.InjOn (starClause G) S := fun _ _ _ _ heq =>
    starClause_injective_of_regular3 hreg hn heq
  have hcard : (S.image (starClause G)).card = S.card :=
    card_image_of_injOn hinj
  have hSlo : r / 2 ≤ S.card := by omega
  have hShi : S.card ≤ r := by omega
  have hge := htouch S hSlo hShi
  have hsup :
      ((S.image (starClause G)).biUnion clauseSupport).card =
        (edgesTouching G S).card := by
    rw [biUnion_clauseSupport_star_eq]
    exact card_image_of_injective _ (edgeVar_injective n hn)
  simpa [hcard, hsup] using hge

/-- Touching lower bound from cut expansion once handshaking
`2 |touching| = 3|S| + |∂S|` is available. Packaged for the next prove cycle. -/
theorem touching_card_ge_two_of_handshaking_expansion {n : ℕ} {G : FinGraph n}
    {S : Finset (Fin n)}
    (hshake : 2 * (edgesTouching G S).card =
      3 * S.card + (edgeBoundary G S).card)
    (hbd : S.card ≤ (edgeBoundary G S).card) :
    2 * S.card ≤ (edgesTouching G S).card := by omega

/-- Heawood star CNF calibration target. -/
def heawoodStarCNF : CNF := starCNF heawoodGraph

theorem heawoodStarCNF_cnfWidth_le : cnfWidth heawoodStarCNF ≤ 3 :=
  starCNF_cnfWidth_le heawoodGraph_regular (by decide : (0 : ℕ) < 14)

/-- Honest: all positive star clauses are satisfiable. -/
theorem heawoodStarCNF_satisfiable : Satisfiable heawoodStarCNF := by
  refine ⟨fun _ => true, ?_⟩
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.mp hC
  have hdeg : (incident heawoodGraph v).card = 3 := heawoodGraph_regular v
  obtain ⟨e, he⟩ :=
    card_pos.mp (show 0 < (incident heawoodGraph v).card from by omega)
  refine ⟨⟨edgeVar e, true⟩, ?_, by simp [litSat]⟩
  simp only [starClause, parityForbidClause, mem_image]
  exact ⟨e, he, rfl⟩

theorem heawoodStarCNF_floor_not_informative :
    ¬ cnfWidth heawoodStarCNF <
        csClauseWidthFloor (heawoodGraph.card / 4) 1 := by
  intro h
  have hr : heawoodGraph.card / 4 = 5 := by simp [heawoodGraph_card]
  have hC : starClause heawoodGraph (0 : Fin 14) ∈ heawoodStarCNF :=
    mem_image.mpr ⟨(0 : Fin 14), mem_univ _, rfl⟩
  have hcard :
      (starClause heawoodGraph (0 : Fin 14)).card = 3 :=
    starClause_card_of_regular3 heawoodGraph_regular (by decide) (0 : Fin 14)
  have hle :
      (starClause heawoodGraph (0 : Fin 14)).card ≤ cnfWidth heawoodStarCNF :=
    Finset.le_sup (f := Finset.card) hC
  have hw : 3 ≤ cnfWidth heawoodStarCNF := by omega
  have : 3 < csClauseWidthFloor 5 1 := by simpa [hr] using lt_of_le_of_lt hw h
  simp [csClauseWidthFloor] at this

/-- Support system form of Spreads (probabilistic method packaging). -/
def SpreadsSupports (U : Finset (Finset ℕ)) (r γ : ℕ) : Prop :=
  ∀ G : Finset (Finset ℕ), G ⊆ U →
    r / 2 ≤ G.card → G.card ≤ r →
      γ * G.card ≤ (G.biUnion id).card

/-- If clause supports are injective into a spreading set system, Spreads holds. -/
theorem spreads_of_spreadsSupports {F : CNF} {r γ : ℕ}
    (hinj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → clauseSupport C ≠ clauseSupport D)
    (hsp : SpreadsSupports (F.image clauseSupport) r γ) :
    Spreads F r γ := by
  intro H hH hlo hhi
  have himg : H.image clauseSupport ⊆ F.image clauseSupport := by
    intro T hT
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hT
    exact mem_image_of_mem _ (hH hC)
  have hinjH : Set.InjOn clauseSupport H := by
    intro C hC D hD hEq
    by_contra hne
    exact hinj C (hH hC) D (hH hD) hne hEq
  have hcard : (H.image clauseSupport).card = H.card :=
    card_image_of_injOn hinjH
  have hlo' : r / 2 ≤ (H.image clauseSupport).card := by omega
  have hhi' : (H.image clauseSupport).card ≤ r := by omega
  have hcov := hsp (H.image clauseSupport) himg hlo' hhi'
  have hU :
      (H.image clauseSupport).biUnion id = H.biUnion clauseSupport := by
    ext x
    constructor
    · intro hx
      obtain ⟨T, hT, hxT⟩ := mem_biUnion.mp hx
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hT
      exact mem_biUnion.mpr ⟨C, hC, by simpa using hxT⟩
    · intro hx
      obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨clauseSupport C, mem_image_of_mem _ hC, hxC⟩
  simpa [hcard, hU] using hcov

/-! ## Frontier: restated existence plus quarantined variable-side names

Critical path existence is `exists_cs_clause_expanding_3cnf` (clause-set pin).
Sufficient accepted route: produce matchable unsat 3-CNF with `Spreads F (n/4) 2`,
then apply `hasCSClauseExpansion_one_of_spreads_two`. Obsolete variable-side
Frontier theorems remain for archival reference only; do not spend cycles proving
them.

Cycle 2026-08-10 (informative push): cubic cages such as LCF McGee on 24 verts
admit vertex cut expansion through r = 9 (so r = |E|/4 is combinatorially in
range), but the formal Tseitin CNF places several clauses on the same triple
support and therefore fails Spreads. Sparse one clause per triple packings that
Spreads at r ≥ 8 stay satisfiable under matchability searches. No honest
informative inhabitant this cycle.

Cycle 2026-08-10 (star encoding): certified `starCNF`, support union identity,
`spreads_starCNF_of_touching_ge`, handshaking packaging lemma, Heawood star
satisfiability and non informative floor, plus `SpreadsSupports`. Remaining:
prove cubic handshaking `2|touching|=3|S|+|∂S|` then instantiate Heawood or
McGee scale Spreads; unsat polarity or probabilistic existence still open. -/

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
