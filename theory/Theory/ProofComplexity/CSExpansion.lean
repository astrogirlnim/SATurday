import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
cubic handshaking `handshaking_touching_of_regular3` plus
`spreads_starCNF_of_expansion` yield Spreads from `HasExpansion _ 1`;
`spreads_heawoodStarCNF_five` instantiates the Heawood cage (satisfiable,
floor not informative). `SpreadsSupports` packages the probabilistic set system
form. Cluster 15 certifies matching triple `SpreadsSupports` at informative
`r ≥ 8`, polarity independent parity supports, and the Spreads or SpreadsSupports
bridge. Cluster 16 certifies overlapping loose path `SpreadsSupports` at
informative scale, polarity triple CNF encoding, and the matching polarity
satisfiability obstruction; matchable unsat polarity on an overlapping system
(or a probabilistic lift) remains open.

Cluster 17 (probabilistic lift scaffolding): finite ensemble
`Oriented3Clause` / `EnsembleIndex` / `Ensemble3CNF`, sample map `random3CNF`
at locked density `m = 6 n` and scale `r = n / 4`, width and variable-card
lemmas, `Spreads.mono_r`, and packaging
`exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`. Cluster 18:
unsat first-moment Nat bounds (`seven_pow_six_lt_two_pow_seventeen`,
`two_pow_mul_seven_pow_lt_eight_pow`, `exists_unsat_random3CNF`). Cluster 19:
Spreads and matchability union bound scaffolding
(`Oriented3Clause.support`, concentration fibers, index Spreads lift,
`isCSMatchable_of_unsat_min_card`). Cluster 20: Spreads summed choose
packaging (`indexSupportFin`, failure terms, card comparison bridge) plus
honest obstruction that the crude `C(m,s) C(n,2s-1) (u/n)^{3s}` close fails
at locked `n = 32`. Frontier `exists_spreads_matchable_unsat_random3CNF`
still open pending a tighter count or parameter revision.

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
`2 |touching| = 3|S| + |∂S|` is available. -/
theorem touching_card_ge_two_of_handshaking_expansion {n : ℕ} {G : FinGraph n}
    {S : Finset (Fin n)}
    (hshake : 2 * (edgesTouching G S).card =
      3 * S.card + (edgeBoundary G S).card)
    (hbd : S.card ≤ (edgeBoundary G S).card) :
    2 * S.card ≤ (edgesTouching G S).card := by omega

/-! ### Cubic handshaking for star encoding Spreads -/

/-- How many endpoints of `e` lie in `S` (0, 1, or 2). -/
def endpointCountIn {n : ℕ} (S : Finset (Fin n)) (e : FinEdge n) : ℕ :=
  (if e.val.1 ∈ S then 1 else 0) + (if e.val.2 ∈ S then 1 else 0)

/-- For a fixed edge, summing endpoint indicators over `S` recovers `endpointCountIn`. -/
theorem sum_endpoint_indicator_eq_endpointCountIn {n : ℕ} (S : Finset (Fin n))
    (e : FinEdge n) :
    ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
      endpointCountIn S e := by
  classical
  by_cases h1 : e.val.1 ∈ S
  · by_cases h2 : e.val.2 ∈ S
    · have hne : e.val.1 ≠ e.val.2 := e.ne_endpoints
      have hfilter :
          (S.filter fun v => e.val.1 = v ∨ e.val.2 = v) =
            ({e.val.1, e.val.2} : Finset (Fin n)) := by
        ext v
        constructor
        · intro hv
          obtain ⟨_, hends⟩ := mem_filter.mp hv
          cases hends with
          | inl h => simp [h]
          | inr h => simp [h]
        · intro hv
          have hv' : v = e.val.1 ∨ v = e.val.2 := by
            simpa [mem_insert, mem_singleton] using hv
          cases hv' with
          | inl h => exact mem_filter.mpr ⟨h ▸ h1, Or.inl h.symm⟩
          | inr h => exact mem_filter.mpr ⟨h ▸ h2, Or.inr h.symm⟩
      have hsum :
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) = 2 := by
        have h1' :
            ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
              (S.filter fun v => e.val.1 = v ∨ e.val.2 = v).sum
                fun _ => (1 : ℕ) :=
          (sum_filter (p := fun v : Fin n => e.val.1 = v ∨ e.val.2 = v)
            (f := fun _ => (1 : ℕ))).symm
        calc
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
              (S.filter fun v => e.val.1 = v ∨ e.val.2 = v).sum
                fun _ => (1 : ℕ) := h1'
          _ = ({e.val.1, e.val.2} : Finset (Fin n)).card := by
            simp [hfilter, sum_const]
          _ = 2 := by simp [hne]
      simpa [endpointCountIn, h1, h2] using hsum
    · have hfilter :
          (S.filter fun v => e.val.1 = v ∨ e.val.2 = v) =
            ({e.val.1} : Finset (Fin n)) := by
        ext v
        constructor
        · intro hv
          obtain ⟨hvS, hends⟩ := mem_filter.mp hv
          cases hends with
          | inl h => simp [h]
          | inr h => exact (h2 (h ▸ hvS)).elim
        · intro hv
          have hv1 : v = e.val.1 := mem_singleton.mp hv
          exact mem_filter.mpr ⟨hv1 ▸ h1, Or.inl hv1.symm⟩
      have hsum :
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) = 1 := by
        have h1' :
            ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
              (S.filter fun v => e.val.1 = v ∨ e.val.2 = v).sum
                fun _ => (1 : ℕ) :=
          (sum_filter (p := fun v : Fin n => e.val.1 = v ∨ e.val.2 = v)
            (f := fun _ => (1 : ℕ))).symm
        calc
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
              (S.filter fun v => e.val.1 = v ∨ e.val.2 = v).sum
                fun _ => (1 : ℕ) := h1'
          _ = 1 := by simp [hfilter, sum_const]
      simpa [endpointCountIn, h1, h2] using hsum
  · by_cases h2 : e.val.2 ∈ S
    · have hfilter :
          (S.filter fun v => e.val.1 = v ∨ e.val.2 = v) =
            ({e.val.2} : Finset (Fin n)) := by
        ext v
        constructor
        · intro hv
          obtain ⟨hvS, hends⟩ := mem_filter.mp hv
          cases hends with
          | inl h => exact (h1 (h ▸ hvS)).elim
          | inr h => simp [h]
        · intro hv
          have hv2 : v = e.val.2 := mem_singleton.mp hv
          exact mem_filter.mpr ⟨hv2 ▸ h2, Or.inr hv2.symm⟩
      have hsum :
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) = 1 := by
        have h1' :
            ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
              (S.filter fun v => e.val.1 = v ∨ e.val.2 = v).sum
                fun _ => (1 : ℕ) :=
          (sum_filter (p := fun v : Fin n => e.val.1 = v ∨ e.val.2 = v)
            (f := fun _ => (1 : ℕ))).symm
        calc
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
              (S.filter fun v => e.val.1 = v ∨ e.val.2 = v).sum
                fun _ => (1 : ℕ) := h1'
          _ = 1 := by simp [hfilter, sum_const]
      simpa [endpointCountIn, h1, h2] using hsum
    · have hsum :
          ∑ v ∈ S, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) = 0 := by
        refine sum_eq_zero fun v hv => ?_
        split_ifs with h
        · cases h with
          | inl heq => exact (h1 (heq ▸ hv)).elim
          | inr heq => exact (h2 (heq ▸ hv)).elim
        · rfl
      simpa [endpointCountIn, h1, h2] using hsum

/-- Double count: sum of degrees over `S` equals sum of endpoint counts in `G`. -/
theorem sum_degree_eq_sum_endpointCountIn {n : ℕ} (G : FinGraph n)
    (S : Finset (Fin n)) :
    ∑ v ∈ S, degree G v = ∑ e ∈ G, endpointCountIn S e := by
  classical
  have hleft :
      ∑ v ∈ S, degree G v =
        ∑ v ∈ S, ∑ e ∈ G,
          (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) := by
    refine sum_congr rfl fun v _ => ?_
    have h1 :
        ∑ e ∈ G, (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
          (G.filter fun e => e.val.1 = v ∨ e.val.2 = v).sum
            fun _ => (1 : ℕ) :=
      (sum_filter (p := fun e : FinEdge n => e.val.1 = v ∨ e.val.2 = v)
        (f := fun _ => (1 : ℕ))).symm
    simpa [degree, incident, sum_const] using h1.symm
  have hswap :
      ∑ v ∈ S, ∑ e ∈ G,
          (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) =
        ∑ e ∈ G, ∑ v ∈ S,
          (if e.val.1 = v ∨ e.val.2 = v then (1 : ℕ) else 0) :=
    sum_comm
  rw [hleft, hswap]
  exact sum_congr rfl fun e _ => sum_endpoint_indicator_eq_endpointCountIn S e

/-- Handshaking on cuts: ∑ deg = 2|internal| + |∂S|. -/
theorem sum_degree_eq_two_internal_add_boundary {n : ℕ} (G : FinGraph n)
    (S : Finset (Fin n)) :
    ∑ v ∈ S, degree G v =
      2 * (edgesInternal G S).card + (edgeBoundary G S).card := by
  classical
  set I := edgesInternal G S
  set B := edgeBoundary G S
  have hIsub : I ⊆ G := fun e he => (mem_edgesInternal_iff.mp he).1
  have hBsub : B ⊆ G := edgeBoundary_subset G S
  have hdisj : Disjoint I B := disjoint_edgesInternal_edgeBoundary G S
  have hpt : ∀ e ∈ G, endpointCountIn S e =
      if e ∈ I then (2 : ℕ) else if e ∈ B then 1 else 0 := by
    intro e heG
    by_cases hI : e ∈ I
    · obtain ⟨_, ha, hb⟩ := mem_edgesInternal_iff.mp hI
      simp [endpointCountIn, hI, ha, hb]
    · by_cases hB : e ∈ B
      · obtain ⟨_, hcut⟩ := mem_edgeBoundary_iff.mp hB
        cases hcut with
        | inl h => simp [endpointCountIn, hI, hB, h.1, h.2]
        | inr h => simp [endpointCountIn, hI, hB, h.1, h.2]
      · have ha : e.val.1 ∉ S := by
          intro hx
          by_cases hb : e.val.2 ∈ S
          · exact hI (mem_edgesInternal_iff.mpr ⟨heG, hx, hb⟩)
          · exact hB (mem_edgeBoundary_iff.mpr ⟨heG, Or.inl ⟨hx, hb⟩⟩)
        have hb : e.val.2 ∉ S := by
          intro hx
          exact hB (mem_edgeBoundary_iff.mpr ⟨heG, Or.inr ⟨ha, hx⟩⟩)
        simp [endpointCountIn, hI, hB, ha, hb]
  have hfilterI : G.filter (fun e => e ∈ I) = I := by
    ext e
    exact ⟨fun he => (mem_filter.mp he).2, fun he => mem_filter.mpr ⟨hIsub he, he⟩⟩
  have hfilterB : G.filter (fun e => e ∉ I ∧ e ∈ B) = B := by
    ext e
    constructor
    · intro he
      exact (mem_filter.mp he).2.2
    · intro he
      exact mem_filter.mpr ⟨hBsub he, ⟨fun hI =>
        (disjoint_left.mp hdisj hI he), he⟩⟩
  have hsum := sum_degree_eq_sum_endpointCountIn G S
  -- Split the edge sum by the internal predicate, then by the boundary predicate.
  have hsplit₁ :=
    (sum_filter_add_sum_filter_not (s := G) (p := fun e => e ∈ I)
      (f := endpointCountIn S)).symm
  have hIconst :
      ∑ e ∈ G.filter (fun e => e ∈ I), endpointCountIn S e = 2 * I.card := by
    have h :
        ∑ e ∈ G.filter (fun e => e ∈ I), endpointCountIn S e =
          ∑ e ∈ I, (2 : ℕ) := by
      refine sum_congr hfilterI fun e he => ?_
      obtain ⟨_, ha, hb⟩ := mem_edgesInternal_iff.mp he
      simp [endpointCountIn, ha, hb]
    simpa [sum_const, mul_comm] using h
  have hsplit₂ :
      ∑ e ∈ G.filter (fun e => e ∉ I), endpointCountIn S e =
        ∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∈ B), endpointCountIn S e +
          ∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∉ B), endpointCountIn S e := by
    -- On `G.filter (∉ I)`, split by membership in `B`.
    have h :=
      (sum_filter_add_sum_filter_not
        (s := G.filter (fun e => e ∉ I)) (p := fun e => e ∈ B)
        (f := endpointCountIn S)).symm
    -- Rewrite the two filtered sets into the ∧ forms.
    have hB' :
        (G.filter (fun e => e ∉ I)).filter (fun e => e ∈ B) =
          G.filter (fun e => e ∉ I ∧ e ∈ B) := by
      ext e; simp [mem_filter, and_comm, and_left_comm]
    have hnB' :
        (G.filter (fun e => e ∉ I)).filter (fun e => e ∉ B) =
          G.filter (fun e => e ∉ I ∧ e ∉ B) := by
      ext e; simp [mem_filter, and_comm, and_left_comm]
    simpa [hB', hnB'] using h
  have hBconst :
      ∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∈ B), endpointCountIn S e = B.card := by
    have h :
        ∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∈ B), endpointCountIn S e =
          ∑ e ∈ B, (1 : ℕ) := by
      refine sum_congr hfilterB fun e he => ?_
      obtain ⟨_, hcut⟩ := mem_edgeBoundary_iff.mp he
      cases hcut with
      | inl hc => simp [endpointCountIn, hc.1, hc.2]
      | inr hc => simp [endpointCountIn, hc.1, hc.2]
    simpa [sum_const] using h
  have hRest :
      ∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∉ B), endpointCountIn S e = 0 := by
    refine sum_eq_zero fun e he => ?_
    obtain ⟨heG, hni, hnb⟩ := mem_filter.mp he
    have hval := hpt e heG
    simp [hni, hnb] at hval
    exact hval
  calc
    ∑ v ∈ S, degree G v = ∑ e ∈ G, endpointCountIn S e := hsum
    _ = ∑ e ∈ G.filter (fun e => e ∈ I), endpointCountIn S e +
          ∑ e ∈ G.filter (fun e => e ∉ I), endpointCountIn S e := hsplit₁
    _ = 2 * I.card +
          (∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∈ B), endpointCountIn S e +
            ∑ e ∈ G.filter (fun e => e ∉ I ∧ e ∉ B), endpointCountIn S e) := by
      rw [hIconst, hsplit₂]
    _ = 2 * I.card + (B.card + 0) := by rw [hBconst, hRest]
    _ = 2 * I.card + B.card := by omega

/-- Touching edges partition into internal edges and the cut. -/
theorem card_edgesTouching_eq_internal_add_boundary {n : ℕ} (G : FinGraph n)
    (S : Finset (Fin n)) :
    (edgesTouching G S).card =
      (edgesInternal G S).card + (edgeBoundary G S).card := by
  rw [edgesTouching_eq_internal_union_boundary,
    card_union_of_disjoint (disjoint_edgesInternal_edgeBoundary G S)]

/-- Cubic handshaking identity: `2 |touching| = 3|S| + |∂S|`. -/
theorem handshaking_touching_of_regular3 {n : ℕ} {G : FinGraph n}
    (hreg : IsRegular G 3) (S : Finset (Fin n)) :
    2 * (edgesTouching G S).card =
      3 * S.card + (edgeBoundary G S).card := by
  have hdeg : ∑ v ∈ S, degree G v = 3 * S.card := by
    calc
      ∑ v ∈ S, degree G v = ∑ v ∈ S, (3 : ℕ) :=
        sum_congr rfl fun v _ => hreg v
      _ = 3 * S.card := by simp [sum_const, mul_comm]
  have hsum := sum_degree_eq_two_internal_add_boundary G S
  have htouch := card_edgesTouching_eq_internal_add_boundary G S
  omega

/-- Expander bridge: cubic `HasExpansion _ 1` yields Spreads for `starCNF` at scale
`r` whenever medium sets sit inside the expansion window `2 * card ≤ n`. -/
theorem spreads_starCNF_of_expansion {n : ℕ} {G : FinGraph n} {r : ℕ}
    (hreg : IsRegular G 3) (hexp : HasExpansion G 1) (hn : 0 < n)
    (hrWin : 2 * r ≤ n) (hrLo : 1 ≤ r / 2) :
    Spreads (starCNF G) r 2 := by
  refine spreads_starCNF_of_touching_ge hreg hn ?_
  intro S hlo hhi
  have hne : S.Nonempty := by
    have : 0 < S.card := lt_of_lt_of_le (Nat.succ_le_iff.mp hrLo) hlo
    exact card_pos.mp this
  have hHalf : 2 * S.card ≤ n := by omega
  have hbd : S.card ≤ (edgeBoundary G S).card := by
    simpa [one_mul] using hexp S hne hHalf
  exact touching_card_ge_two_of_handshaking_expansion
    (handshaking_touching_of_regular3 hreg S) hbd

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

/-- Heawood star CNF Spreads at cage scale `r = 5` via cubic handshaking plus
`heawoodGraph_expansion`. Honest: formula remains satisfiable and the α = 1 floor
at this scale is not informative. -/
theorem spreads_heawoodStarCNF_five : Spreads heawoodStarCNF 5 2 := by
  have hrWin : 2 * (5 : ℕ) ≤ 14 := by decide
  have hrLo : 1 ≤ (5 : ℕ) / 2 := by decide
  simpa [heawoodStarCNF] using
    spreads_starCNF_of_expansion heawoodGraph_regular heawoodGraph_expansion
      (by decide : (0 : ℕ) < 14) hrWin hrLo

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

/-! ## SpreadsSupports scaffolding (changed approach: set system first)

Prior cycles blocked on all positive star CNF satisfiability at cage scale and on
finite sparse unsat search. Spreads cares only about supports, so the
probabilistic route factors as (1) inhabit `SpreadsSupports` at informative
`r ≥ 8`, then (2) choose polarities yielding matchable unsat. This cluster
certifies (1) for disjoint triple matchings, polarity independent supports for
parity forbidding clauses, and the Spreads ↔ SpreadsSupports bridge under
injective supports. Step (2) remains the Frontier gap. -/

/-- Weaker spreading rate is inherited. -/
theorem SpreadsSupports.mono_gamma {U : Finset (Finset ℕ)} {r γ γ' : ℕ}
    (h : SpreadsSupports U r γ) (hle : γ' ≤ γ) :
    SpreadsSupports U r γ' := by
  intro G hG hlo hhi
  have hge := h G hG hlo hhi
  exact le_trans (Nat.mul_le_mul_right G.card hle) hge

/-- Support of a parity forbidding clause depends only on the incident star, not
on the polarity set `S`. -/
theorem clauseSupport_parityForbidClause {n : ℕ}
    (I S : Finset (FinEdge n)) :
    clauseSupport (parityForbidClause I S) = I.image edgeVar := by
  ext x
  constructor
  · intro hx
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hl
    exact mem_image.mpr ⟨e, he, rfl⟩
  · intro hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    refine mem_image.mpr ⟨⟨edgeVar e, decide (e ∉ S)⟩, ?_, rfl⟩
    exact mem_image.mpr ⟨e, he, rfl⟩

/-- Star clause with an arbitrary polarity set on the incident edges. -/
def starClauseWith {n : ℕ} (G : FinGraph n) (v : Fin n)
    (S : Finset (FinEdge n)) : Clause :=
  parityForbidClause (incident G v) S

theorem clauseSupport_starClauseWith {n : ℕ} (G : FinGraph n) (v : Fin n)
    (S : Finset (FinEdge n)) :
    clauseSupport (starClauseWith G v S) = (incident G v).image edgeVar :=
  clauseSupport_parityForbidClause _ _

theorem clauseSupport_starClauseWith_eq_starClause {n : ℕ}
    (G : FinGraph n) (v : Fin n) (S : Finset (FinEdge n)) :
    clauseSupport (starClauseWith G v S) = clauseSupport (starClause G v) := by
  rw [clauseSupport_starClauseWith, clauseSupport_starClause]

/-- Selected polarity star CNF: one forbidding clause per vertex. -/
def starCNFWith {n : ℕ} (G : FinGraph n)
    (sel : Fin n → Finset (FinEdge n)) : CNF :=
  (univ : Finset (Fin n)).image fun v => starClauseWith G v (sel v)

/-- Under injective supports, Spreads yields SpreadsSupports on the support image. -/
theorem spreadsSupports_of_spreads {F : CNF} {r γ : ℕ}
    (_hinj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → clauseSupport C ≠ clauseSupport D)
    (hsp : Spreads F r γ) :
    SpreadsSupports (F.image clauseSupport) r γ := by
  intro G hG hlo hhi
  classical
  -- Choose, for each support in G, a unique owning clause in F.
  let owner : Finset ℕ → Clause := fun T =>
    if h : ∃ C ∈ F, clauseSupport C = T then Classical.choose h else ∅
  have howner : ∀ T ∈ G, owner T ∈ F ∧ clauseSupport (owner T) = T := by
    intro T hT
    have hEx : ∃ C ∈ F, clauseSupport C = T := by
      obtain ⟨C, hC, rfl⟩ := mem_image.mp (hG hT)
      exact ⟨C, hC, rfl⟩
    simpa [owner, dif_pos hEx] using Classical.choose_spec hEx
  let H : Finset Clause := G.image owner
  have hHsub : H ⊆ F := by
    intro C hC
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hC
    exact (howner T hT).1
  have hInjOwner : Set.InjOn owner G := by
    intro T hT T' hT' hEq
    have h1 := (howner T hT).2
    have h2 := (howner T' hT').2
    calc
      T = clauseSupport (owner T) := h1.symm
      _ = clauseSupport (owner T') := by rw [hEq]
      _ = T' := h2
  have hcard : H.card = G.card := card_image_of_injOn hInjOwner
  have hloH : r / 2 ≤ H.card := by omega
  have hhiH : H.card ≤ r := by omega
  have hcov := hsp H hHsub hloH hhiH
  have hU : H.biUnion clauseSupport = G.biUnion id := by
    ext x
    constructor
    · intro hx
      obtain ⟨C, hC, hxC⟩ := mem_biUnion.mp hx
      obtain ⟨T, hT, rfl⟩ := mem_image.mp hC
      have hCT : clauseSupport (owner T) = T := (howner T hT).2
      exact mem_biUnion.mpr ⟨T, hT, by simpa [hCT] using hxC⟩
    · intro hx
      obtain ⟨T, hT, hxT⟩ := mem_biUnion.mp hx
      refine mem_biUnion.mpr ⟨owner T, mem_image_of_mem _ hT, ?_⟩
      have hCT : clauseSupport (owner T) = T := (howner T hT).2
      simpa [hCT] using hxT
  simpa [hcard, hU] using hcov

/-- Disjoint triple `{3i, 3i+1, 3i+2}` used as a matching support block. -/
def matchingTriple (i : ℕ) : Finset ℕ :=
  ({3 * i, 3 * i + 1, 3 * i + 2} : Finset ℕ)

theorem matchingTriple_card (i : ℕ) : (matchingTriple i).card = 3 := by
  -- The three indices 3i, 3i+1, 3i+2 are pairwise distinct.
  simp [matchingTriple]

theorem matchingTriple_disjoint {i j : ℕ} (hne : i ≠ j) :
    Disjoint (matchingTriple i) (matchingTriple j) := by
  refine disjoint_left.mpr ?_
  intro x hxI hxJ
  have hxI' : x = 3 * i ∨ x = 3 * i + 1 ∨ x = 3 * i + 2 := by
    simpa [matchingTriple, mem_insert, mem_singleton] using hxI
  have hxJ' : x = 3 * j ∨ x = 3 * j + 1 ∨ x = 3 * j + 2 := by
    simpa [matchingTriple, mem_insert, mem_singleton] using hxJ
  have hle_i : 3 * i ≤ x ∧ x ≤ 3 * i + 2 := by
    rcases hxI' with h | h | h <;> omega
  have hle_j : 3 * j ≤ x ∧ x ≤ 3 * j + 2 := by
    rcases hxJ' with h | h | h <;> omega
  have : i = j := by omega
  exact hne this

theorem matchingTriple_injective {i j : ℕ}
    (h : matchingTriple i = matchingTriple j) : i = j := by
  by_contra hne
  have hdis := matchingTriple_disjoint hne
  have hne' : matchingTriple i ≠ matchingTriple j := by
    intro heq
    have hmem : (3 * i : ℕ) ∈ matchingTriple i := by
      simp [matchingTriple]
    have : (3 * i : ℕ) ∈ matchingTriple j := by simpa [heq] using hmem
    exact (disjoint_left.mp hdis) hmem this
  exact hne' h

/-- Matching support system: `m` pairwise disjoint triples. -/
def matchingTripleSupports (m : ℕ) : Finset (Finset ℕ) :=
  (range m).image matchingTriple

theorem mem_matchingTripleSupports {m : ℕ} {T : Finset ℕ} :
    T ∈ matchingTripleSupports m ↔ ∃ i < m, matchingTriple i = T := by
  simp [matchingTripleSupports, mem_image]

theorem matchingTripleSupports_card (m : ℕ) :
    (matchingTripleSupports m).card = m := by
  classical
  simpa [matchingTripleSupports] using
    (card_image_of_injective (range m)
      (fun {i j : ℕ} (h : matchingTriple i = matchingTriple j) =>
        matchingTriple_injective h))

/-- Any subcollection of a matching covers three fresh variables per triple. -/
theorem card_biUnion_matchingTripleSupports_subset {m : ℕ}
    {G : Finset (Finset ℕ)} (hG : G ⊆ matchingTripleSupports m) :
    (G.biUnion id).card = 3 * G.card := by
  classical
  revert hG
  refine Finset.induction_on G ?_ ?_
  · intro _; simp
  · intro T G hT IH hG'
    have hTmem : T ∈ matchingTripleSupports m := hG' (mem_insert_self _ _)
    have hGsub : G ⊆ matchingTripleSupports m :=
      (subset_insert _ _).trans hG'
    obtain ⟨i, hi, rfl⟩ := mem_matchingTripleSupports.mp hTmem
    have hdis : Disjoint (matchingTriple i) (G.biUnion id) := by
      refine disjoint_left.mpr ?_
      intro x hxT hxU
      obtain ⟨T', hT', hxT'⟩ := mem_biUnion.mp hxU
      have hT'mem : T' ∈ matchingTripleSupports m := hGsub hT'
      obtain ⟨j, hj, rfl⟩ := mem_matchingTripleSupports.mp hT'mem
      have hne : i ≠ j := by
        intro heq
        have : matchingTriple i ∈ G := by simpa [heq] using hT'
        exact hT this
      exact (disjoint_left.mp (matchingTriple_disjoint hne)) hxT hxT'
    have hcardT : (matchingTriple i).card = 3 := matchingTriple_card i
    calc
      ((insert (matchingTriple i) G).biUnion id).card =
          ((matchingTriple i) ∪ G.biUnion id).card := by
            simp [biUnion_insert]
      _ = (matchingTriple i).card + (G.biUnion id).card :=
          card_union_of_disjoint hdis
      _ = 3 + (G.biUnion id).card := by rw [hcardT]
      _ = 3 + 3 * G.card := by rw [IH hGsub]
      _ = 3 * (G.card + 1) := by omega
      _ = 3 * (insert (matchingTriple i) G).card := by
            rw [card_insert_of_notMem hT]

/-- Matching triples SpreadsSupports at rate 3 up to the matching size. -/
theorem spreadsSupports_matchingTriples (m r : ℕ) (_hr : r ≤ m) :
    SpreadsSupports (matchingTripleSupports m) r 3 := by
  intro G hG _hlo _hhi
  have hcard := card_biUnion_matchingTripleSupports_subset hG
  have : 3 * G.card ≤ (G.biUnion id).card := by omega
  exact this

/-- Matching triples also SpreadsSupports at the CS rate γ = 2. -/
theorem spreadsSupports_matchingTriples_two (m r : ℕ) (hr : r ≤ m) :
    SpreadsSupports (matchingTripleSupports m) r 2 :=
  SpreadsSupports.mono_gamma (spreadsSupports_matchingTriples m r hr) (by omega)

/-- Non vacuous set system witness at the informative floor threshold `r = 8`. -/
theorem exists_spreadsSupports_informative :
    ∃ (U : Finset (Finset ℕ)) (r : ℕ),
      8 ≤ r ∧ SpreadsSupports U r 2 :=
  ⟨matchingTripleSupports 8, 8, le_rfl,
    spreadsSupports_matchingTriples_two 8 8 le_rfl⟩

/-- One concrete informative scale witness packages the matching of size 8. -/
theorem spreadsSupports_matchingTriples_eight :
    SpreadsSupports (matchingTripleSupports 8) 8 2 :=
  spreadsSupports_matchingTriples_two 8 8 le_rfl

/-! ## Overlapping SpreadsSupports and polarity CNF packaging

Matching systems SpreadsSupports at every scale but admit satisfying polarity
assignments (each triple is independent). The next constructive step is an
overlapping support system that still SpreadsSupports at informative `r ≥ 8`,
together with a polarity encoding from supports to width-3 CNFs. Unsat polarity
on such a system (or a probabilistic lift) remains the Frontier gap. -/

/-- Width-3 clause on support `T` with per-variable polarity `p`. -/
def triplePolarityClause (T : Finset ℕ) (p : ℕ → Bool) : Clause :=
  T.image fun x => (⟨x, p x⟩ : Literal)

theorem clauseSupport_triplePolarityClause (T : Finset ℕ) (p : ℕ → Bool) :
    clauseSupport (triplePolarityClause T p) = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hl
    exact hy
  · intro hx
    refine mem_image.mpr ⟨⟨x, p x⟩, ?_, rfl⟩
    exact mem_image.mpr ⟨x, hx, rfl⟩

theorem triplePolarityClause_card (T : Finset ℕ) (p : ℕ → Bool) :
    (triplePolarityClause T p).card = T.card := by
  classical
  refine card_image_of_injective T ?_
  intro x y h
  exact congrArg Literal.var h

/-- One polarity clause per support block. -/
def cnfOfSupports (U : Finset (Finset ℕ)) (p : Finset ℕ → ℕ → Bool) : CNF :=
  U.image fun T => triplePolarityClause T (p T)

theorem mem_cnfOfSupports {U : Finset (Finset ℕ)} {p : Finset ℕ → ℕ → Bool}
    {C : Clause} :
    C ∈ cnfOfSupports U p ↔
      ∃ T ∈ U, triplePolarityClause T (p T) = C := by
  simp [cnfOfSupports, mem_image]

theorem cnfOfSupports_cnfWidth_le (U : Finset (Finset ℕ))
    (p : Finset ℕ → ℕ → Bool)
    (h3 : ∀ T ∈ U, T.card ≤ 3) :
    cnfWidth (cnfOfSupports U p) ≤ 3 := by
  refine Finset.sup_le ?_
  intro C hC
  obtain ⟨T, hT, rfl⟩ := mem_cnfOfSupports.mp hC
  have hcard : (triplePolarityClause T (p T)).card = T.card :=
    triplePolarityClause_card T (p T)
  have hT3 : T.card ≤ 3 := h3 T hT
  omega

/-- Image of supports recovers `U` for any polarity map. -/
theorem image_clauseSupport_cnfOfSupports {U : Finset (Finset ℕ)}
    (p : Finset ℕ → ℕ → Bool) :
    (cnfOfSupports U p).image clauseSupport = U := by
  ext T
  constructor
  · intro hT
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hT
    obtain ⟨T', hT', rfl⟩ := mem_cnfOfSupports.mp hC
    simpa [clauseSupport_triplePolarityClause] using hT'
  · intro hT
    refine mem_image.mpr ⟨triplePolarityClause T (p T), ?_, ?_⟩
    · exact mem_cnfOfSupports.mpr ⟨T, hT, rfl⟩
    · exact clauseSupport_triplePolarityClause T (p T)

/-- Under SpreadsSupports, the polarity CNF inherits Spreads. -/
theorem spreads_cnfOfSupports_of_spreadsSupports {U : Finset (Finset ℕ)}
    {p : Finset ℕ → ℕ → Bool} {r γ : ℕ}
    (hsp : SpreadsSupports U r γ) :
    Spreads (cnfOfSupports U p) r γ := by
  have himg := image_clauseSupport_cnfOfSupports (U := U) p
  have hinj :
      ∀ C ∈ cnfOfSupports U p, ∀ D ∈ cnfOfSupports U p, C ≠ D →
        clauseSupport C ≠ clauseSupport D := by
    intro C hC D hD hne hEq
    obtain ⟨T, hT, rfl⟩ := mem_cnfOfSupports.mp hC
    obtain ⟨T', hT', rfl⟩ := mem_cnfOfSupports.mp hD
    have hTe :
        clauseSupport (triplePolarityClause T (p T)) =
          clauseSupport (triplePolarityClause T' (p T')) := hEq
    have : T = T' := by
      simpa [clauseSupport_triplePolarityClause] using hTe
    exact hne (by simpa [this])
  have himg' :
      SpreadsSupports ((cnfOfSupports U p).image clauseSupport) r γ := by
    simpa [himg] using hsp
  exact spreads_of_spreadsSupports hinj himg'

/-- Disjoint support blocks: any polarity assignment is satisfiable. -/
theorem satisfiable_cnfOfSupports_of_pairwise_disjoint
    (U : Finset (Finset ℕ)) (p : Finset ℕ → ℕ → Bool)
    (hdis : ∀ T ∈ U, ∀ T' ∈ U, T ≠ T' → Disjoint T T')
    (hne : ∀ T ∈ U, T.Nonempty) :
    Satisfiable (cnfOfSupports U p) := by
  classical
  -- On each block set variables to the clause polarity; disjointness keeps this consistent.
  let a : Assignment := fun x =>
    if h : ∃ T ∈ U, x ∈ T then
      let T := Classical.choose h
      p T x
    else
      true
  refine ⟨a, ?_⟩
  intro C hC
  obtain ⟨T, hT, rfl⟩ := mem_cnfOfSupports.mp hC
  obtain ⟨x, hx⟩ := hne T hT
  refine ⟨⟨x, p T x⟩, ?_, ?_⟩
  · exact mem_image.mpr ⟨x, hx, rfl⟩
  · have hex : ∃ T' ∈ U, x ∈ T' := ⟨T, hT, hx⟩
    have hTeq : Classical.choose hex = T := by
      have hspec := Classical.choose_spec hex
      have hdis' := hdis (Classical.choose hex) hspec.1 T hT
      by_cases hneT : Classical.choose hex = T
      · exact hneT
      · exact False.elim ((disjoint_left.mp (hdis' hneT)) hspec.2 hx)
    simp [litSat, a, dif_pos hex, hTeq]

/-- Matching triples are pairwise disjoint, so every polarity CNF is satisfiable. -/
theorem satisfiable_matchingTripleSupports_cnf (m : ℕ)
    (p : Finset ℕ → ℕ → Bool) :
    Satisfiable (cnfOfSupports (matchingTripleSupports m) p) := by
  refine satisfiable_cnfOfSupports_of_pairwise_disjoint _ p ?_ ?_
  · intro T hT T' hT' hne
    obtain ⟨i, hi, rfl⟩ := mem_matchingTripleSupports.mp hT
    obtain ⟨j, hj, rfl⟩ := mem_matchingTripleSupports.mp hT'
    have hij : i ≠ j := fun heq => hne (by simpa [heq])
    exact matchingTriple_disjoint hij
  · intro T hT
    obtain ⟨i, hi, rfl⟩ := mem_matchingTripleSupports.mp hT
    refine ⟨3 * i, ?_⟩
    simp [matchingTriple]

/-- Overlapping path block `{2i, 2i+1, 2i+2}` (adjacent blocks share one vertex). -/
def loosePathTriple (i : ℕ) : Finset ℕ :=
  ({2 * i, 2 * i + 1, 2 * i + 2} : Finset ℕ)

theorem loosePathTriple_card (i : ℕ) : (loosePathTriple i).card = 3 := by
  simp [loosePathTriple]

theorem loosePathTriple_injective {i j : ℕ}
    (h : loosePathTriple i = loosePathTriple j) : i = j := by
  have hi : (2 * i + 1 : ℕ) ∈ loosePathTriple i := by simp [loosePathTriple]
  have hj : (2 * i + 1 : ℕ) ∈ loosePathTriple j := by simpa [h] using hi
  have hj' : 2 * i + 1 = 2 * j ∨ 2 * i + 1 = 2 * j + 1 ∨ 2 * i + 1 = 2 * j + 2 := by
    simpa [loosePathTriple, mem_insert, mem_singleton] using hj
  rcases hj' with h1 | h2 | h3
  · omega
  · omega
  · omega

/-- Adjacent path triples share exactly the glue vertex `2i+2`. -/
theorem loosePathTriple_inter_succ (i : ℕ) :
    loosePathTriple i ∩ loosePathTriple (i + 1) = ({2 * i + 2} : Finset ℕ) := by
  ext x
  constructor
  · intro hx
    have hxI := (mem_inter.mp hx).1
    have hxJ := (mem_inter.mp hx).2
    have hxI' : x = 2 * i ∨ x = 2 * i + 1 ∨ x = 2 * i + 2 := by
      simpa [loosePathTriple, mem_insert, mem_singleton] using hxI
    have hxJ' : x = 2 * (i + 1) ∨ x = 2 * (i + 1) + 1 ∨ x = 2 * (i + 1) + 2 := by
      simpa [loosePathTriple, mem_insert, mem_singleton] using hxJ
    rcases hxI' with h0 | h1 | h2
    · rcases hxJ' with j0 | j1 | j2 <;> omega
    · rcases hxJ' with j0 | j1 | j2 <;> omega
    · simp [h2]
  · intro hx
    have : x = 2 * i + 2 := mem_singleton.mp hx
    subst this
    refine mem_inter.mpr ⟨?_, ?_⟩
    · simp [loosePathTriple]
    · -- `2i+2` is the left endpoint of the successor block.
      have : (2 * i + 2 : ℕ) = 2 * (i + 1) := by omega
      simpa [loosePathTriple, this]

/-- Non adjacent path triples are disjoint. -/
theorem loosePathTriple_disjoint_of_far {i j : ℕ} (h : 2 ≤ i - j ∨ 2 ≤ j - i) :
    Disjoint (loosePathTriple i) (loosePathTriple j) := by
  refine disjoint_left.mpr ?_
  intro x hxI hxJ
  have hxI' : x = 2 * i ∨ x = 2 * i + 1 ∨ x = 2 * i + 2 := by
    simpa [loosePathTriple, mem_insert, mem_singleton] using hxI
  have hxJ' : x = 2 * j ∨ x = 2 * j + 1 ∨ x = 2 * j + 2 := by
    simpa [loosePathTriple, mem_insert, mem_singleton] using hxJ
  rcases h with hji | hij
  · rcases hxI' with h0 | h1 | h2 <;> rcases hxJ' with j0 | j1 | j2 <;> omega
  · rcases hxI' with h0 | h1 | h2 <;> rcases hxJ' with j0 | j1 | j2 <;> omega

/-- Overlapping path support system of length `m`. -/
def loosePathSupports (m : ℕ) : Finset (Finset ℕ) :=
  (range m).image loosePathTriple

theorem mem_loosePathSupports {m : ℕ} {T : Finset ℕ} :
    T ∈ loosePathSupports m ↔ ∃ i < m, loosePathTriple i = T := by
  simp [loosePathSupports, mem_image]

theorem loosePathSupports_card (m : ℕ) : (loosePathSupports m).card = m := by
  classical
  simpa [loosePathSupports] using
    (card_image_of_injective (range m)
      (fun {i j : ℕ} (h : loosePathTriple i = loosePathTriple j) =>
        loosePathTriple_injective h))

/-- Adjacent overlap witness: path length at least 2 is genuinely overlapping. -/
theorem loosePathSupports_overlaps {m : ℕ} (hm : 2 ≤ m) :
    ∃ T ∈ loosePathSupports m, ∃ T' ∈ loosePathSupports m,
      T ≠ T' ∧ (T ∩ T').Nonempty := by
  refine ⟨loosePathTriple 0, ?_, loosePathTriple 1, ?_, ?_, ?_⟩
  · exact mem_loosePathSupports.mpr ⟨0, by omega, rfl⟩
  · exact mem_loosePathSupports.mpr ⟨1, by omega, rfl⟩
  · intro h
    have : (0 : ℕ) = 1 := loosePathTriple_injective h
    exact (by omega : False)
  · rw [loosePathTriple_inter_succ]
    exact singleton_nonempty _

/-- Index set form of a path subcollection. -/
def loosePathIndexSet {m : ℕ} (G : Finset (Finset ℕ))
    (hG : G ⊆ loosePathSupports m) : Finset ℕ :=
  (range m).filter fun i => loosePathTriple i ∈ G

theorem mem_loosePathIndexSet {m : ℕ} {G : Finset (Finset ℕ)}
    (hG : G ⊆ loosePathSupports m) {i : ℕ} :
    i ∈ loosePathIndexSet G hG ↔ i < m ∧ loosePathTriple i ∈ G := by
  simp [loosePathIndexSet, mem_filter]

theorem card_loosePathIndexSet {m : ℕ} {G : Finset (Finset ℕ)}
    (hG : G ⊆ loosePathSupports m) :
    (loosePathIndexSet G hG).card = G.card := by
  classical
  have himg :
      (loosePathIndexSet G hG).image loosePathTriple = G := by
    ext T
    constructor
    · intro hT
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hT
      exact ((mem_loosePathIndexSet hG).mp hi).2
    · intro hT
      obtain ⟨i, hi, rfl⟩ := mem_loosePathSupports.mp (hG hT)
      exact mem_image.mpr ⟨i, (mem_loosePathIndexSet hG).mpr ⟨hi, hT⟩, rfl⟩
  have hinj : Set.InjOn loosePathTriple (loosePathIndexSet G hG : Set ℕ) := by
    intro i _ j _ hEq
    exact loosePathTriple_injective hEq
  calc
    (loosePathIndexSet G hG).card =
        ((loosePathIndexSet G hG).image loosePathTriple).card :=
      (card_image_of_injOn hinj).symm
    _ = G.card := by rw [himg]

/-- Union size of a path subcollection: `|I|` private odds plus the even glue cover. -/
theorem card_biUnion_loosePathSupports_subset {m : ℕ}
    {G : Finset (Finset ℕ)} (hG : G ⊆ loosePathSupports m) :
    2 * G.card ≤ (G.biUnion id).card := by
  classical
  set I := loosePathIndexSet G hG
  have hIcard : I.card = G.card := card_loosePathIndexSet hG
  let Evens : Finset ℕ :=
    I.biUnion fun i => ({2 * i, 2 * i + 2} : Finset ℕ)
  let Odds : Finset ℕ := I.image fun i => 2 * i + 1
  have hU :
      G.biUnion id = Evens ∪ Odds := by
    ext x
    constructor
    · intro hx
      obtain ⟨T, hT, hxT⟩ := mem_biUnion.mp hx
      obtain ⟨i, hi, rfl⟩ := mem_loosePathSupports.mp (hG hT)
      have hiI : i ∈ I := (mem_loosePathIndexSet hG).mpr ⟨hi, hT⟩
      have hx' : x = 2 * i ∨ x = 2 * i + 1 ∨ x = 2 * i + 2 := by
        simpa [loosePathTriple, mem_insert, mem_singleton] using hxT
      rcases hx' with h0 | h1 | h2
      · exact mem_union_left _ (mem_biUnion.mpr ⟨i, hiI, by simp [h0]⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨i, hiI, h1.symm⟩)
      · exact mem_union_left _ (mem_biUnion.mpr ⟨i, hiI, by simp [h2]⟩)
    · intro hx
      rcases mem_union.mp hx with hxE | hxO
      · obtain ⟨i, hiI, hxE'⟩ := mem_biUnion.mp hxE
        have hT : loosePathTriple i ∈ G := ((mem_loosePathIndexSet hG).mp hiI).2
        have hx' : x = 2 * i ∨ x = 2 * i + 2 := by
          simpa [mem_insert, mem_singleton] using hxE'
        refine mem_biUnion.mpr ⟨loosePathTriple i, hT, ?_⟩
        rcases hx' with h0 | h2
        · simpa [loosePathTriple, h0]
        · simpa [loosePathTriple, h2]
      · obtain ⟨i, hiI, rfl⟩ := mem_image.mp hxO
        have hT : loosePathTriple i ∈ G := ((mem_loosePathIndexSet hG).mp hiI).2
        exact mem_biUnion.mpr ⟨loosePathTriple i, hT, by simp [loosePathTriple]⟩
  have hdisEO : Disjoint Evens Odds := by
    refine disjoint_left.mpr ?_
    intro x hxE hxO
    obtain ⟨i, _, hxE'⟩ := mem_biUnion.mp hxE
    have : x = 2 * i ∨ x = 2 * i + 2 := by
      simpa [mem_insert, mem_singleton] using hxE'
    obtain ⟨j, _, rfl⟩ := mem_image.mp hxO
    rcases this with h0 | h2 <;> omega
  have hOdds : Odds.card = I.card := by
    refine card_image_of_injective I ?_
    intro a b hEq
    have h' : 2 * a + 1 = 2 * b + 1 := hEq
    omega
  have hLeftInj : Function.Injective fun i : ℕ => 2 * i := by
    intro a b hEq
    have h' : 2 * a = 2 * b := hEq
    omega
  have hLefts : (I.image fun i => 2 * i).card = I.card :=
    card_image_of_injective I hLeftInj
  have hLefts_sub : I.image (fun i => 2 * i) ⊆ Evens := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_biUnion.mpr ⟨i, hi, by simp⟩
  have hEvens_ge : I.card ≤ Evens.card := by
    calc
      I.card = (I.image fun i => 2 * i).card := hLefts.symm
      _ ≤ Evens.card := card_le_card hLefts_sub
  have : 2 * I.card ≤ (Evens ∪ Odds).card := by
    have hsum : (Evens ∪ Odds).card = Evens.card + Odds.card :=
      card_union_of_disjoint hdisEO
    omega
  simpa [hU, hIcard] using this

/-- Overlapping path SpreadsSupports at rate 2 up to path length. -/
theorem spreadsSupports_loosePath (m r : ℕ) (_hr : r ≤ m) :
    SpreadsSupports (loosePathSupports m) r 2 := by
  intro G hG _hlo _hhi
  exact card_biUnion_loosePathSupports_subset hG

/-- Informative overlapping SpreadsSupports witness (path length 16, scale 8). -/
theorem exists_overlapping_spreadsSupports_informative :
    ∃ (U : Finset (Finset ℕ)) (r : ℕ),
      8 ≤ r ∧ SpreadsSupports U r 2 ∧
        (∃ T ∈ U, ∃ T' ∈ U, T ≠ T' ∧ (T ∩ T').Nonempty) :=
  ⟨loosePathSupports 16, 8, le_rfl,
    spreadsSupports_loosePath 16 8 (by omega),
    loosePathSupports_overlaps (by omega)⟩

/-- Concrete overlapping informative package. -/
theorem spreadsSupports_loosePath_sixteen :
    SpreadsSupports (loosePathSupports 16) 8 2 :=
  spreadsSupports_loosePath 16 8 (by omega)

/-- All-true polarity on the informative overlapping path remains satisfiable
(hypertree obstruction; overlap alone does not force unsat). -/
theorem satisfiable_loosePathSupports_allTrue (m : ℕ) :
    Satisfiable
      (cnfOfSupports (loosePathSupports m) fun _ _ => true) := by
  classical
  refine ⟨fun _ => true, ?_⟩
  intro C hC
  obtain ⟨T, hT, rfl⟩ := mem_cnfOfSupports.mp hC
  obtain ⟨i, hi, rfl⟩ := mem_loosePathSupports.mp hT
  refine ⟨⟨2 * i, true⟩, ?_, ?_⟩
  · simp [triplePolarityClause, loosePathTriple]
  · simp [litSat]

/-! ## Probabilistic lift scaffolding (pinned plan, density m = 6 n)

Finite ensemble for the Chvatal–Szemeredi / Ben-Sasson–Wigderson random 3-CNF
route into `exists_cs_clause_expanding_3cnf`. No probability axiom: samples are
ordinary functions `Fin m → Oriented3Clause n`, and existence is a finite
pigeonhole claim. Counting bounds that close the existence stay Frontier. -/

/-- One oriented 3-literal atom on variables in `Fin n` (duplicates collapse in
the clause Finset, so width stays at most 3). -/
structure Oriented3Clause (n : ℕ) where
  x : Fin n
  y : Fin n
  z : Fin n
  px : Bool
  py : Bool
  pz : Bool
deriving DecidableEq, Repr

/-- Convert an oriented atom to a clause (at most three literals). -/
def Oriented3Clause.toClause {n : ℕ} (c : Oriented3Clause n) : Clause :=
  ({⟨c.x.val, c.px⟩, ⟨c.y.val, c.py⟩, ⟨c.z.val, c.pz⟩} : Clause)

theorem Oriented3Clause.toClause_card_le {n : ℕ} (c : Oriented3Clause n) :
    c.toClause.card ≤ 3 := by
  classical
  simp only [Oriented3Clause.toClause]
  have h1 :=
    card_insert_le (⟨c.x.val, c.px⟩ : Literal)
      ({⟨c.y.val, c.py⟩, ⟨c.z.val, c.pz⟩} : Clause)
  have h2 :=
    card_insert_le (⟨c.y.val, c.py⟩ : Literal)
      ({⟨c.z.val, c.pz⟩} : Clause)
  have h3 : ({⟨c.z.val, c.pz⟩} : Clause).card ≤ 1 := by
    simpa using (card_singleton (⟨c.z.val, c.pz⟩ : Literal))
  omega

theorem Oriented3Clause.mem_toClause_var_lt {n : ℕ} (c : Oriented3Clause n)
    {v : ℕ} (hv : v ∈ clauseVars c.toClause) : v < n := by
  simp only [Oriented3Clause.toClause, clauseVars, mem_image, mem_insert,
    mem_singleton] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  rcases hl with h | h | h <;> subst h <;> exact Fin.is_lt _

/-- Sample index: length-`m` sequence of oriented 3-clauses on `n` variables. -/
abbrev EnsembleIndex (n m : ℕ) := Fin m → Oriented3Clause n

/-- Finite sample space of the random 3-CNF ensemble (alias of `EnsembleIndex`). -/
abbrev Ensemble3CNF (n m : ℕ) := EnsembleIndex n m

/-- Locked density Δ = 6 from the accepted probabilistic plan. -/
def random3CNFDensity : ℕ := 6

/-- Clause count at locked density: `m = 6 * n`. -/
def random3CNFClauseCount (n : ℕ) : ℕ := random3CNFDensity * n

/-- Matchability and Spreads scale in the pin: `r = n / 4`. -/
def random3CNFMatchScale (n : ℕ) : ℕ := n / 4

theorem random3CNFClauseCount_eq (n : ℕ) :
    random3CNFClauseCount n = 6 * n := by
  simp [random3CNFClauseCount, random3CNFDensity]

/-- Informative floor for α = 1 requires `r ≥ 8`, hence `n ≥ 32` under `r = n/4`. -/
theorem random3CNFMatchScale_ge_eight {n : ℕ} (hn : 32 ≤ n) :
    8 ≤ random3CNFMatchScale n := by
  simp only [random3CNFMatchScale]
  omega

theorem csClauseWidthFloor_of_random3CNFMatchScale {n : ℕ} (hn : 32 ≤ n) :
    3 < csClauseWidthFloor (random3CNFMatchScale n) 1 := by
  have hr : 8 ≤ random3CNFMatchScale n := random3CNFMatchScale_ge_eight hn
  simp only [csClauseWidthFloor, random3CNFMatchScale] at hr ⊢
  omega

/-- Concrete CNF at sample `ω`: image of the `m` oriented clauses (duplicates
collapse under Finset). -/
def random3CNF (n m : ℕ) (ω : EnsembleIndex n m) : CNF :=
  (univ : Finset (Fin m)).image fun i => (ω i).toClause

theorem mem_random3CNF {n m : ℕ} {ω : EnsembleIndex n m} {C : Clause} :
    C ∈ random3CNF n m ω ↔ ∃ i : Fin m, (ω i).toClause = C := by
  simp [random3CNF, mem_image]

/-- Every sample is a width-at-most-3 CNF by construction. -/
theorem random3CNF_cnfWidth_le (n m : ℕ) (ω : EnsembleIndex n m) :
    cnfWidth (random3CNF n m ω) ≤ 3 := by
  refine Finset.sup_le ?_
  intro C hC
  obtain ⟨i, rfl⟩ := (mem_random3CNF (ω := ω)).mp hC
  exact Oriented3Clause.toClause_card_le (ω i)

/-- Variables of any sample lie in `range n`. -/
theorem random3CNF_vars_subset_range (n m : ℕ) (ω : EnsembleIndex n m) :
    cnfVars (random3CNF n m ω) ⊆ range n := by
  intro v hv
  obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
  obtain ⟨i, rfl⟩ := (mem_random3CNF (ω := ω)).mp hC
  exact mem_range.mpr (Oriented3Clause.mem_toClause_var_lt (ω i) hvC)

/-- Variable support is at most `n` (pin uses equality after restricting to used
variables, via mono lemmas). -/
theorem random3CNF_vars_card (n m : ℕ) (ω : EnsembleIndex n m) :
    (cnfVars (random3CNF n m ω)).card ≤ n := by
  have hsub := random3CNF_vars_subset_range n m ω
  exact (card_le_card hsub).trans (by simp [card_range])

/-- Ensemble is inhabited whenever there is at least one variable (needed so
existence over samples is a nonempty finite search). -/
theorem ensembleIndex_nonempty {n m : ℕ} (hn : 0 < n) :
    Nonempty (EnsembleIndex n m) := by
  refine ⟨fun _ => ?_⟩
  refine ⟨⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩, true, true, true⟩

/-- Spreads transfers to a smaller scale when the smaller medium interval sits
inside the larger one (`r/2 ≤ r'/2` and `r' ≤ r`). -/
theorem Spreads.mono_r {F : CNF} {r r' γ : ℕ}
    (h : Spreads F r γ) (hlo : r / 2 ≤ r' / 2) (hhi : r' ≤ r) :
    Spreads F r' γ := by
  intro G hG hlo' hhi'
  exact h G hG (le_trans hlo hlo') (le_trans hhi' hhi)

/-- Packaging: matchable unsat Spreads at rate 2 and scale `n/4` yields the
critical-path clause-set expansion inhabitant (α = 1). -/
theorem exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat
    (h : ∀ N : ℕ, ∃ (n : ℕ) (F : CNF),
      N ≤ n ∧ (cnfVars F).card = n ∧ cnfWidth F ≤ 3 ∧
        Spreads F (n / 4) 2 ∧ IsCSMatchable F (n / 4) ∧ ¬ Satisfiable F ∧
          cnfWidth F < csClauseWidthFloor (n / 4) 1) :
    ∀ N : ℕ, ∃ (n : ℕ) (F : CNF) (r α : ℕ),
      N ≤ n ∧ (cnfVars F).card = n ∧ cnfWidth F ≤ 3 ∧
        α = 1 ∧ r = n / 4 ∧
          IsCSMatchable F r ∧ HasCSClauseExpansion F r α ∧
            ¬ Satisfiable F ∧ cnfWidth F < csClauseWidthFloor r α := by
  intro N
  obtain ⟨n, F, hN, hvars, hw, hsp, hmatch, hunsat, hfloor⟩ := h N
  refine ⟨n, F, n / 4, 1, hN, hvars, hw, rfl, rfl, hmatch, ?_, hunsat, ?_⟩
  · exact hasCSClauseExpansion_one_of_spreads_two hw hsp
  · simpa [csClauseWidthFloor] using hfloor

/-! ## Unsat first-moment Nat bounds (Cluster 18)

Finite counting for Step 2 of the probabilistic plan: a fixed `Fin n`
assignment satisfies a uniform oriented 3-clause on exactly `7 n^3` of the
`8 n^3` atoms, so at density `m = 6 n` the union bound is
`2^n · 7^(6n) < 8^(6n)`, which is the Nat packaging of
`2^n (7/8)^(6n) → 0`. No analysis axioms: only `7^6 < 2^17`. -/

/-- Product encoding of an oriented atom (for Fintype cardinality). -/
def Oriented3Clause.equivProd (n : ℕ) :
    Oriented3Clause n ≃ (Fin n × Fin n × Fin n × Bool × Bool × Bool) where
  toFun c := (c.x, c.y, c.z, c.px, c.py, c.pz)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {n : ℕ} : Fintype (Oriented3Clause n) :=
  Fintype.ofEquiv _ (Oriented3Clause.equivProd n).symm

theorem card_oriented3Clause (n : ℕ) :
    Fintype.card (Oriented3Clause n) = 8 * n ^ 3 := by
  rw [Fintype.card_congr (Oriented3Clause.equivProd n)]
  simp [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Literal satisfaction under `assignmentOfFin` on a variable in `Fin n`. -/
theorem litSat_assignmentOfFin {n : ℕ} (χ : Fin n → Bool) (i : Fin n)
    (p : Bool) :
    litSat (assignmentOfFin χ) ⟨i.val, p⟩ ↔ χ i = p := by
  simp [litSat, assignmentOfFin, i.isLt]

/-- An oriented atom is satisfied by `χ` iff at least one of its three
polarities matches `χ` on that coordinate (duplicates in the Finset clause do
not change the disjunction). -/
theorem clauseSat_toClause_iff {n : ℕ} (c : Oriented3Clause n)
    (χ : Fin n → Bool) :
    clauseSat (assignmentOfFin χ) c.toClause ↔
      c.px = χ c.x ∨ c.py = χ c.y ∨ c.pz = χ c.z := by
  classical
  constructor
  · intro ⟨l, hl, hsat⟩
    simp only [Oriented3Clause.toClause, mem_insert, mem_singleton] at hl
    rcases hl with hl | hl | hl <;> subst hl
    · left; exact (litSat_assignmentOfFin χ c.x c.px).mp hsat |>.symm
    · right; left; exact (litSat_assignmentOfFin χ c.y c.py).mp hsat |>.symm
    · right; right; exact (litSat_assignmentOfFin χ c.z c.pz).mp hsat |>.symm
  · intro h
    rcases h with h | h | h
    · refine ⟨⟨c.x.val, c.px⟩, ?_,
        (litSat_assignmentOfFin χ c.x c.px).mpr h.symm⟩
      simp [Oriented3Clause.toClause]
    · refine ⟨⟨c.y.val, c.py⟩, ?_,
        (litSat_assignmentOfFin χ c.y c.py).mpr h.symm⟩
      simp [Oriented3Clause.toClause]
    · refine ⟨⟨c.z.val, c.pz⟩, ?_,
        (litSat_assignmentOfFin χ c.z c.pz).mpr h.symm⟩
      simp [Oriented3Clause.toClause]

/-- Unique falsifying polarity pattern for a fixed triple and assignment. -/
theorem not_clauseSat_toClause_iff {n : ℕ} (c : Oriented3Clause n)
    (χ : Fin n → Bool) :
    ¬ clauseSat (assignmentOfFin χ) c.toClause ↔
      c.px = !χ c.x ∧ c.py = !χ c.y ∧ c.pz = !χ c.z := by
  rw [clauseSat_toClause_iff, not_or, not_or]
  cases χ c.x <;> cases χ c.y <;> cases χ c.z <;> cases c.px <;>
    cases c.py <;> cases c.pz <;> decide

/-- Exactly `n^3` oriented atoms falsify a fixed `Fin n` assignment. -/
theorem card_oriented3Clause_unsat {n : ℕ} (χ : Fin n → Bool) :
    Fintype.card
        { c : Oriented3Clause n //
          ¬ clauseSat (assignmentOfFin χ) c.toClause } =
      n ^ 3 := by
  classical
  let e :
      Fin n × Fin n × Fin n ≃
        { c : Oriented3Clause n //
          ¬ clauseSat (assignmentOfFin χ) c.toClause } :=
    { toFun := fun p =>
        ⟨⟨p.1, p.2.1, p.2.2, !χ p.1, !χ p.2.1, !χ p.2.2⟩, by
          rw [not_clauseSat_toClause_iff]; simp⟩
      invFun := fun c => (c.1.x, c.1.y, c.1.z)
      left_inv := fun _ => rfl
      right_inv := fun c => by
        have h := (not_clauseSat_toClause_iff c.1 χ).mp c.2
        apply Subtype.ext
        obtain ⟨⟨x, y, z, px, py, pz⟩, hc⟩ := c
        change Oriented3Clause.mk x y z (!χ x) (!χ y) (!χ z) =
          Oriented3Clause.mk x y z px py pz
        have hx : px = !χ x := h.1
        have hy : py = !χ y := h.2.1
        have hz : pz = !χ z := h.2.2
        subst hx; subst hy; subst hz
        rfl }
  simpa [Fintype.card_prod, Fintype.card_fin, pow_three] using
    (Fintype.card_congr e).symm

/-- Exactly `7 n^3` oriented atoms satisfy a fixed `Fin n` assignment. -/
theorem card_oriented3Clause_sat {n : ℕ} (χ : Fin n → Bool) :
    Fintype.card
        { c : Oriented3Clause n //
          clauseSat (assignmentOfFin χ) c.toClause } =
      7 * n ^ 3 := by
  classical
  have htot := card_oriented3Clause n
  have hunsat := card_oriented3Clause_unsat χ
  have hcompl :=
    Fintype.card_subtype_compl fun c : Oriented3Clause n =>
      clauseSat (assignmentOfFin χ) c.toClause
  have hle :
      Fintype.card
          { c : Oriented3Clause n //
            clauseSat (assignmentOfFin χ) c.toClause } ≤
        Fintype.card (Oriented3Clause n) :=
    Fintype.card_subtype_le _
  have hadd :
      Fintype.card
          { c : Oriented3Clause n //
            clauseSat (assignmentOfFin χ) c.toClause } +
        Fintype.card
          { c : Oriented3Clause n //
            ¬ clauseSat (assignmentOfFin χ) c.toClause } =
        Fintype.card (Oriented3Clause n) := by
    rw [Nat.add_comm, hcompl, Nat.sub_add_cancel hle]
  rw [htot, hunsat] at hadd
  omega

/-- Satisfaction of the sampled CNF is clausewise on the oriented sequence. -/
theorem cnfSat_random3CNF_iff {n m : ℕ} {ω : EnsembleIndex n m}
    {a : Assignment} :
    cnfSat a (random3CNF n m ω) ↔
      ∀ i : Fin m, clauseSat a (ω i).toClause := by
  constructor
  · intro h i
    exact h _ ((mem_random3CNF (ω := ω)).mpr ⟨i, rfl⟩)
  · intro h C hC
    obtain ⟨i, rfl⟩ := (mem_random3CNF (ω := ω)).mp hC
    exact h i

/-- Ensemble cardinality: `(8 n^3)^m`. -/
theorem card_ensembleIndex (n m : ℕ) :
    Fintype.card (EnsembleIndex n m) = (8 * n ^ 3) ^ m := by
  rw [Fintype.card_fun, Fintype.card_fin, card_oriented3Clause]

/-- Fixed assignment fiber: exactly `(7 n^3)^m` satisfying samples. -/
theorem card_ensembleIndex_sat {n m : ℕ} (χ : Fin n → Bool) :
    Fintype.card
        { ω : EnsembleIndex n m //
          cnfSat (assignmentOfFin χ) (random3CNF n m ω) } =
      (7 * n ^ 3) ^ m := by
  classical
  let e :
      { ω : EnsembleIndex n m //
          cnfSat (assignmentOfFin χ) (random3CNF n m ω) } ≃
        (Fin m →
          { c : Oriented3Clause n //
            clauseSat (assignmentOfFin χ) c.toClause }) :=
    { toFun := fun ω i =>
        ⟨ω.1 i, (cnfSat_random3CNF_iff (a := assignmentOfFin χ)).mp ω.2 i⟩
      invFun := fun τ =>
        ⟨fun i => (τ i).1, by
          rw [cnfSat_random3CNF_iff]
          intro i; exact (τ i).2⟩
      left_inv := fun _ => by
        ext <;> rfl
      right_inv := fun _ => by
        ext <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
    card_oriented3Clause_sat]

/-- Core Nat inequality: `7^6 = 117649 < 131072 = 2^17`. -/
theorem seven_pow_six_lt_two_pow_seventeen : 7 ^ 6 < 2 ^ 17 := by
  decide

/-- First-moment comparison at density `m = 6 n`: `2^n · 7^(6n) < 8^(6n)`. -/
theorem two_pow_mul_seven_pow_lt_eight_pow {n : ℕ} (hn : 0 < n) :
    2 ^ n * 7 ^ (6 * n) < 8 ^ (6 * n) := by
  have hbase : 7 ^ 6 < 2 ^ 17 := seven_pow_six_lt_two_pow_seventeen
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hpow : (7 ^ 6) ^ n < (2 ^ 17) ^ n :=
    Nat.pow_lt_pow_left hbase hne
  have h7 : 7 ^ (6 * n) < 2 ^ (17 * n) := by
    -- `Nat.pow_mul a m n` : `a ^ (m * n) = (a ^ m) ^ n`
    have e1 : 7 ^ (6 * n) = (7 ^ 6) ^ n := Nat.pow_mul 7 6 n
    have e2 : 2 ^ (17 * n) = (2 ^ 17) ^ n := Nat.pow_mul 2 17 n
    rw [e1, e2]
    exact hpow
  have h2pos : 0 < 2 ^ n := Nat.pow_pos (by decide : (0 : ℕ) < 2)
  have hmul : 2 ^ n * 7 ^ (6 * n) < 2 ^ n * 2 ^ (17 * n) :=
    Nat.mul_lt_mul_of_pos_left h7 h2pos
  have hsum : 2 ^ n * 2 ^ (17 * n) = 2 ^ (18 * n) := by
    rw [← Nat.pow_add]
    congr 1
    ring
  have h8 : 8 ^ (6 * n) = 2 ^ (18 * n) := by
    have : (8 : ℕ) = 2 ^ 3 := by decide
    rw [this, ← Nat.pow_mul]
    congr 1
    ring
  calc
    2 ^ n * 7 ^ (6 * n) < 2 ^ n * 2 ^ (17 * n) := hmul
    _ = 2 ^ (18 * n) := hsum
    _ = 8 ^ (6 * n) := h8.symm

/-- Cancel `(n^3)^m` to obtain the sample-space form of the first moment. -/
theorem two_pow_mul_seven_cube_pow_lt_eight_cube_pow {n m : ℕ}
    (hn : 0 < n) (hm : m = 6 * n) :
    2 ^ n * (7 * n ^ 3) ^ m < (8 * n ^ 3) ^ m := by
  have hn3 : 0 < n ^ 3 := Nat.pow_pos hn
  have hcore := two_pow_mul_seven_pow_lt_eight_pow hn
  subst hm
  have h7 :
      (7 * n ^ 3) ^ (6 * n) = 7 ^ (6 * n) * (n ^ 3) ^ (6 * n) :=
    Nat.mul_pow _ _ _
  have h8 :
      (8 * n ^ 3) ^ (6 * n) = 8 ^ (6 * n) * (n ^ 3) ^ (6 * n) :=
    Nat.mul_pow _ _ _
  have hpos : 0 < (n ^ 3) ^ (6 * n) := Nat.pow_pos hn3
  have hmul := Nat.mul_lt_mul_of_pos_right hcore hpos
  calc
    2 ^ n * (7 * n ^ 3) ^ (6 * n)
        = 2 ^ n * (7 ^ (6 * n) * (n ^ 3) ^ (6 * n)) := by rw [h7]
    _ = (2 ^ n * 7 ^ (6 * n)) * (n ^ 3) ^ (6 * n) := by ring
    _ < (8 ^ (6 * n)) * (n ^ 3) ^ (6 * n) := hmul
    _ = (8 * n ^ 3) ^ (6 * n) := by rw [← h8]

/-- Satisfiable samples inject into the assignment-indexed sat fibers. -/
theorem card_ensembleIndex_le_sat_sum {n m : ℕ}
    (hsat : ∀ ω : EnsembleIndex n m,
      existsSatFin n (random3CNF n m ω)) :
    Fintype.card (EnsembleIndex n m) ≤
      2 ^ n * (7 * n ^ 3) ^ m := by
  classical
  choose χ hχ using hsat
  let f : EnsembleIndex n m →
      Σ τ : Fin n → Bool,
        { ω : EnsembleIndex n m //
          cnfSat (assignmentOfFin τ) (random3CNF n m ω) } :=
    fun ω => ⟨χ ω, ω, hχ ω⟩
  have hinj : Function.Injective f := by
    intro ω₁ ω₂ h
    exact congrArg (fun s : Σ τ : Fin n → Bool,
        { ω : EnsembleIndex n m //
          cnfSat (assignmentOfFin τ) (random3CNF n m ω) } =>
      (s.2 : EnsembleIndex n m)) h
  have hle := Fintype.card_le_of_injective f hinj
  refine hle.trans (le_of_eq ?_)
  rw [Fintype.card_sigma]
  simp only [card_ensembleIndex_sat, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_cast

/-- Exists an unsatisfiable sample at locked density `m = 6 n` for every
`n ≥ 1` (first-moment union bound). -/
theorem exists_unsat_random3CNF {n : ℕ} (hn : 0 < n) :
    ∃ ω : EnsembleIndex n (random3CNFClauseCount n),
      ¬ Satisfiable (random3CNF n (random3CNFClauseCount n) ω) := by
  classical
  set m := random3CNFClauseCount n
  have hm : m = 6 * n := random3CNFClauseCount_eq n
  have hstrict :=
    two_pow_mul_seven_cube_pow_lt_eight_cube_pow hn hm
  by_contra h
  push Not at h
  have hsatfin :
      ∀ ω : EnsembleIndex n m, existsSatFin n (random3CNF n m ω) := by
    intro ω
    obtain ⟨a, ha⟩ := h ω
    refine ⟨fun i => a i.val, ?_⟩
    intro C hC
    obtain ⟨l, hl, hlit⟩ := ha C hC
    refine ⟨l, hl, ?_⟩
    have hv : l.var ∈ cnfVars (random3CNF n m ω) :=
      mem_biUnion.mpr ⟨C, hC, mem_image.mpr ⟨l, hl, rfl⟩⟩
    have hlt : l.var < n :=
      mem_range.mp ((random3CNF_vars_subset_range n m ω) hv)
    simpa [litSat, assignmentOfFin, hlt] using hlit
  have hle := card_ensembleIndex_le_sat_sum hsatfin
  have hcard := card_ensembleIndex n m
  have : (8 * n ^ 3) ^ m ≤ 2 ^ n * (7 * n ^ 3) ^ m := by
    simpa [hcard] using hle
  exact (not_le_of_gt hstrict) this

/-- Convenience: some sample is unsatisfiable for every `n ≥ 32` (informative
scale regime). -/
theorem exists_unsat_random3CNF_ge_thirty_two {n : ℕ} (hn : 32 ≤ n) :
    ∃ ω : EnsembleIndex n (random3CNFClauseCount n),
      ¬ Satisfiable (random3CNF n (random3CNFClauseCount n) ω) :=
  exists_unsat_random3CNF (lt_of_lt_of_le (by decide : (0 : ℕ) < 32) hn)

/-! ## Spreads and matchability union-bound scaffolding (Cluster 19)

Step 3 and Step 4 of the probabilistic plan: combinatorial packaging for the
Spreads concentration event and the matchability extraction from large
minimally unsat cores. Fiber cardinalities mirror Cluster 18 (no analysis
axioms). The summed `∑_s C(m,s) C(n,2s-1) (O(s/n))^{3s}` inequality that
closes the existence remains Frontier. -/

/-- Variable support of an oriented atom as a `ℕ` Finset (at most three). -/
def Oriented3Clause.support {n : ℕ} (c : Oriented3Clause n) : Finset ℕ :=
  insert c.x.val (insert c.y.val ({c.z.val} : Finset ℕ))

theorem Oriented3Clause.support_card_le {n : ℕ} (c : Oriented3Clause n) :
    c.support.card ≤ 3 := by
  classical
  simp only [Oriented3Clause.support]
  have h1 := card_insert_le c.x.val (insert c.y.val ({c.z.val} : Finset ℕ))
  have h2 := card_insert_le c.y.val ({c.z.val} : Finset ℕ)
  have h3 : ({c.z.val} : Finset ℕ).card ≤ 1 := by
    simpa using (card_singleton c.z.val)
  omega

/-- Clause support equals the oriented support Finset. -/
theorem clauseSupport_toClause_eq_support {n : ℕ} (c : Oriented3Clause n) :
    clauseSupport c.toClause = c.support := by
  classical
  ext v
  simp only [clauseSupport, clauseVars, Oriented3Clause.toClause,
    Oriented3Clause.support, mem_image, mem_insert, mem_singleton]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hl with h | h | h <;> subst h <;> simp
  · intro hv
    rcases hv with h | h | h <;> subst h
    · exact ⟨⟨c.x.val, c.px⟩, by simp, rfl⟩
    · exact ⟨⟨c.y.val, c.py⟩, by simp, rfl⟩
    · exact ⟨⟨c.z.val, c.pz⟩, by simp, rfl⟩

/-- Support variables all lie in `range n`. -/
theorem Oriented3Clause.support_subset_range {n : ℕ} (c : Oriented3Clause n) :
    c.support ⊆ range n := by
  intro v hv
  simp only [Oriented3Clause.support, mem_insert, mem_singleton] at hv
  rcases hv with h | h | h <;> subst h <;> exact mem_range.mpr (Fin.is_lt _)

/-- Oriented atoms whose three coordinates land in a fixed `Fin`-set `U`. -/
def Oriented3Clause.memSupport (n : ℕ) (U : Finset (Fin n))
    (c : Oriented3Clause n) : Prop :=
  c.x ∈ U ∧ c.y ∈ U ∧ c.z ∈ U

/-- Exactly `8 |U|^3` oriented atoms are supported inside `U`. -/
theorem card_oriented3Clause_memSupport {n : ℕ} (U : Finset (Fin n)) :
    Fintype.card
        { c : Oriented3Clause n // Oriented3Clause.memSupport n U c } =
      8 * U.card ^ 3 := by
  classical
  let e :
      (U × U × U × Bool × Bool × Bool) ≃
        { c : Oriented3Clause n // Oriented3Clause.memSupport n U c } :=
    { toFun := fun p =>
        ⟨⟨p.1.1, p.2.1.1, p.2.2.1.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩, by
          refine ⟨p.1.2, p.2.1.2, p.2.2.1.2⟩⟩
      invFun := fun c =>
        ⟨⟨c.1.x, c.2.1⟩, ⟨c.1.y, c.2.2.1⟩, ⟨c.1.z, c.2.2.2⟩, c.1.px, c.1.py,
          c.1.pz⟩
      left_inv := fun _ => by
        ext <;> rfl
      right_inv := fun _ => by
        ext <;> rfl }
  rw [Fintype.card_congr e.symm]
  simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  ring

/-- Crude bound: support-in-`U` fiber is at most `8 |U|^3` (and ≤ total). -/
theorem card_oriented3Clause_memSupport_le {n : ℕ} (U : Finset (Fin n)) :
    Fintype.card
        { c : Oriented3Clause n // Oriented3Clause.memSupport n U c } ≤
      8 * U.card ^ 3 :=
  le_of_eq (card_oriented3Clause_memSupport U)

/-- Index set support union under a sample. -/
def indexSupport {n m : ℕ} (ω : EnsembleIndex n m) (S : Finset (Fin m)) :
    Finset ℕ :=
  S.biUnion fun i => (ω i).support

/-- Concentration: every index in `S` has its three coordinates in `U`. -/
def supportConcentrated {n m : ℕ} (ω : EnsembleIndex n m)
    (S : Finset (Fin m)) (U : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, Oriented3Clause.memSupport n U (ω i)

/-- Concentrated index supports sit inside the `ℕ` image of `U`. -/
theorem indexSupport_subset_of_concentrated {n m : ℕ}
    {ω : EnsembleIndex n m} {S : Finset (Fin m)} {U : Finset (Fin n)}
    (h : supportConcentrated ω S U) :
    indexSupport ω S ⊆ U.image Fin.val := by
  intro v hv
  obtain ⟨i, hi, hv'⟩ := mem_biUnion.mp hv
  have hmem := h i hi
  simp only [Oriented3Clause.support, mem_insert, mem_singleton] at hv'
  rcases hv' with hv' | hv' | hv' <;> subst hv'
  · exact mem_image.mpr ⟨(ω i).x, hmem.1, rfl⟩
  · exact mem_image.mpr ⟨(ω i).y, hmem.2.1, rfl⟩
  · exact mem_image.mpr ⟨(ω i).z, hmem.2.2, rfl⟩

/-- Hence concentrated supports have cardinality at most `|U|`. -/
theorem indexSupport_card_le_of_concentrated {n m : ℕ}
    {ω : EnsembleIndex n m} {S : Finset (Fin m)} {U : Finset (Fin n)}
    (h : supportConcentrated ω S U) :
    (indexSupport ω S).card ≤ U.card := by
  have hsub := indexSupport_subset_of_concentrated h
  exact (card_le_card hsub).trans (card_image_le)

/-- Index-level Spreads: medium index sets expand their oriented supports. -/
def SpreadsIndices {n m : ℕ} (ω : EnsembleIndex n m) (r : ℕ) : Prop :=
  ∀ S : Finset (Fin m),
    r / 2 ≤ S.card → S.card ≤ r →
      2 * S.card ≤ (indexSupport ω S).card

/-- Failure of index Spreads yields a medium concentrated witness scale. -/
theorem exists_concentrated_of_not_spreadsIndices {n m : ℕ}
    {ω : EnsembleIndex n m} {r : ℕ} (h : ¬ SpreadsIndices ω r) :
    ∃ S : Finset (Fin m),
      r / 2 ≤ S.card ∧ S.card ≤ r ∧
        (indexSupport ω S).card < 2 * S.card := by
  classical
  unfold SpreadsIndices at h
  push Not at h
  obtain ⟨S, hlo, hhi, hcard⟩ := h
  exact ⟨S, hlo, hhi, hcard⟩

/-- From index Spreads, the sampled CNF Spreads at rate 2 (choose one preimage
index per clause; support unions agree). -/
theorem spreads_random3CNF_of_spreadsIndices {n m : ℕ}
    (ω : EnsembleIndex n m) {r : ℕ} (h : SpreadsIndices ω r) :
    Spreads (random3CNF n m ω) r 2 := by
  classical
  intro G hG hlo hhi
  have hpre :
      ∀ C ∈ G, ∃ i : Fin m, (ω i).toClause = C := by
    intro C hC
    exact (mem_random3CNF (ω := ω)).mp (hG hC)
  choose τ hτ using hpre
  let S : Finset (Fin m) := G.attach.image fun C => τ C.1 C.2
  have hSinj :
      Function.Injective fun C : { x // x ∈ G } => τ C.1 C.2 := by
    intro C₁ C₂ hEq
    apply Subtype.ext
    have hC1 : (ω (τ C₁.1 C₁.2)).toClause = C₁.1 := hτ C₁.1 C₁.2
    have hC2 : (ω (τ C₂.1 C₂.2)).toClause = C₂.1 := hτ C₂.1 C₂.2
    have hsame : (ω (τ C₁.1 C₁.2)).toClause = (ω (τ C₂.1 C₂.2)).toClause := by
      simpa [hEq]
    exact hC1.symm.trans (hsame.trans hC2)
  have hScard : S.card = G.card := by
    change (G.attach.image fun C : { x // x ∈ G } => τ C.1 C.2).card = G.card
    rw [card_image_of_injective G.attach hSinj, card_attach]
  have hSlo : r / 2 ≤ S.card := by simpa [hScard] using hlo
  have hShi : S.card ≤ r := by simpa [hScard] using hhi
  have hExp : 2 * S.card ≤ (indexSupport ω S).card := h S hSlo hShi
  have hsupp :
      ∀ C (hC : C ∈ G),
        clauseSupport C = (ω (τ C hC)).support := by
    intro C hC
    calc
      clauseSupport C = clauseSupport ((ω (τ C hC)).toClause) := by
        rw [hτ C hC]
      _ = (ω (τ C hC)).support := clauseSupport_toClause_eq_support _
  have hU : G.biUnion clauseSupport = indexSupport ω S := by
    ext v
    constructor
    · intro hv
      obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
      refine mem_biUnion.mpr ⟨τ C hC, ?_, ?_⟩
      · exact mem_image.mpr ⟨⟨C, hC⟩, mem_attach _ _, rfl⟩
      · simpa [hsupp C hC] using hvC
    · intro hv
      obtain ⟨i, hi, hv'⟩ := mem_biUnion.mp hv
      obtain ⟨Csub, _, rfl⟩ := mem_image.mp hi
      refine mem_biUnion.mpr ⟨Csub.1, Csub.2, ?_⟩
      simpa [hsupp Csub.1 Csub.2] using hv'
  have : 2 * G.card ≤ (G.biUnion clauseSupport).card := by
    simpa [hScard, hU] using hExp
  exact this

/-- Matchability from a lower bound on every unsatisfiable subset. -/
theorem isCSMatchable_of_unsat_min_card {F : CNF} {r : ℕ}
    (h : ∀ G ⊆ F, ¬ Satisfiable G → r < G.card) :
    IsCSMatchable F r := by
  intro H hH hcard
  by_contra hunsat
  have := h H hH hunsat
  exact (not_lt_of_ge hcard) this

/-- Same extraction specialized to minimally unsat cores. -/
theorem isCSMatchable_of_minimallyUnsat_card_gt {F : CNF} {r : ℕ}
    (_hunsat : ¬ Satisfiable F)
    (h : ∀ G ⊆ F, IsMinimallyUnsat G → r < G.card) :
    IsCSMatchable F r := by
  refine isCSMatchable_of_unsat_min_card ?_
  intro H hH hunH
  obtain ⟨G, hGsub, hGmin⟩ := exists_minimallyUnsat_subset hunH
  have hrG : r < G.card := h G (hGsub.trans hH) hGmin
  exact lt_of_lt_of_le hrG (card_le_card hGsub)

/-- Minimally unsat cores larger than `r` yield matchability at scale `r`. -/
theorem isCSMatchable_of_minimallyUnsat_gt {F : CNF} {r : ℕ}
    (h : IsMinimallyUnsat F) (hr : r < F.card) :
    IsCSMatchable F r :=
  IsCSMatchable.mono (isCSMatchable_of_minimallyUnsat h)
    (Nat.le_pred_of_lt hr)

/-- Negation of matchability is existence of a small unsat subset. -/
theorem exists_unsat_subset_of_not_isCSMatchable {F : CNF} {r : ℕ}
    (h : ¬ IsCSMatchable F r) :
    ∃ G ⊆ F, G.card ≤ r ∧ ¬ Satisfiable G := by
  classical
  unfold IsCSMatchable at h
  push Not at h
  obtain ⟨G, hG, hcard, hunsat⟩ := h
  exact ⟨G, hG, hcard, hunsat⟩

/-- Restricted product: functions on `S` into the `U`-supported atoms. -/
theorem card_fun_memSupport {n m : ℕ} (S : Finset (Fin m))
    (U : Finset (Fin n)) :
    Fintype.card
        (∀ _i : ↥S,
          { c : Oriented3Clause n // Oriented3Clause.memSupport n U c }) =
      (8 * U.card ^ 3) ^ S.card := by
  classical
  rw [Fintype.card_fun, card_oriented3Clause_memSupport, Fintype.card_coe]

/-- Fiber: samples concentrated on `U` along `S`, free elsewhere.
Cardinality `(8 |U|^3)^|S| · (8 n^3)^{m-|S|}`. -/
theorem card_ensembleIndex_supportConcentrated {n m : ℕ}
    (S : Finset (Fin m)) (U : Finset (Fin n)) :
    Fintype.card
        { ω : EnsembleIndex n m // supportConcentrated ω S U } =
      (8 * U.card ^ 3) ^ S.card * (8 * n ^ 3) ^ (m - S.card) := by
  classical
  let Sc : Finset (Fin m) := univ \ S
  have hSdisj : Disjoint S Sc := disjoint_sdiff
  have hSuniv : S ∪ Sc = (univ : Finset (Fin m)) :=
    union_sdiff_of_subset (subset_univ S)
  have hcardSc : Sc.card = m - S.card := by
    have : S.card + Sc.card = m := by
      calc
        S.card + Sc.card = (S ∪ Sc).card :=
          (card_union_of_disjoint hSdisj).symm
        _ = (univ : Finset (Fin m)).card := by rw [hSuniv]
        _ = m := by simp [card_univ, Fintype.card_fin]
    omega
  let e :
      { ω : EnsembleIndex n m // supportConcentrated ω S U } ≃
        ((∀ i : ↥S,
            { c : Oriented3Clause n // Oriented3Clause.memSupport n U c }) ×
          (∀ i : ↥Sc, Oriented3Clause n)) :=
    { toFun := fun ω =>
        (fun i => ⟨ω.1 (i : Fin m), ω.2 (i : Fin m) i.2⟩,
          fun i => ω.1 (i : Fin m))
      invFun := fun τ =>
        ⟨fun i =>
          if hi : i ∈ S then (τ.1 ⟨i, hi⟩).1
          else
            have hiSc : i ∈ Sc := mem_sdiff.mpr ⟨mem_univ i, hi⟩
            τ.2 ⟨i, hiSc⟩,
          by
            intro i hi
            dsimp
            simp [hi]
            exact (τ.1 ⟨i, hi⟩).2⟩
      left_inv := fun ω => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi]
        · have hiSc : i ∈ Sc := mem_sdiff.mpr ⟨mem_univ i, hi⟩
          simp [hi]
      right_inv := fun τ => by
        refine Prod.ext ?_ ?_
        · funext i
          simp [i.2]
        · funext i
          have hi : (i : Fin m) ∉ S := (mem_sdiff.mp i.2).2
          simp [hi] }
  rw [Fintype.card_congr e, Fintype.card_prod]
  have hSfun := card_fun_memSupport (n := n) (m := m) S U
  have hScfun :
      Fintype.card (∀ _i : ↥Sc, Oriented3Clause n) =
        (8 * n ^ 3) ^ Sc.card := by
    classical
    rw [Fintype.card_fun, card_oriented3Clause, Fintype.card_coe]
  rw [hSfun, hScfun, hcardSc]

/-- Ratio form: concentration probability bound as a Nat comparison. -/
theorem card_ensembleIndex_supportConcentrated_mul_lt_iff {n m : ℕ}
    (S : Finset (Fin m)) (U : Finset (Fin n))
    (hpos : 0 < 8 * n ^ 3) :
    (8 * U.card ^ 3) ^ S.card * (8 * n ^ 3) ^ (m - S.card) <
        (8 * n ^ 3) ^ m ↔
      (8 * U.card ^ 3) ^ S.card < (8 * n ^ 3) ^ S.card := by
  have hle : S.card ≤ m := by
    simpa [card_univ, Fintype.card_fin] using
      (card_le_card (subset_univ S) : S.card ≤ (univ : Finset (Fin m)).card)
  have hm : (8 * n ^ 3) ^ m =
      (8 * n ^ 3) ^ S.card * (8 * n ^ 3) ^ (m - S.card) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  constructor
  · intro h
    rw [hm] at h
    exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
  · intro h
    rw [hm]
    exact Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos hpos)

/-- Cancel the common `8^s` factor in the concentration ratio. -/
theorem eight_mul_pow_card_lt_iff {u n s : ℕ} (hs : 0 < s) :
    (8 * u ^ 3) ^ s < (8 * n ^ 3) ^ s ↔ u ^ 3 < n ^ 3 := by
  have h8pos : 0 < (8 : ℕ) := by decide
  have hsne : s ≠ 0 := Nat.pos_iff_ne_zero.mp hs
  constructor
  · intro h
    have hbase : 8 * u ^ 3 < 8 * n ^ 3 :=
      (Nat.pow_lt_pow_iff_left hsne).mp h
    exact lt_of_mul_lt_mul_left hbase (Nat.zero_le _)
  · intro h
    have hmul : 8 * u ^ 3 < 8 * n ^ 3 :=
      Nat.mul_lt_mul_of_pos_left h h8pos
    exact Nat.pow_lt_pow_left hmul hsne

/-- Cube reflects strict inequality on the positive naturals. -/
theorem pow_three_lt_pow_three {u n : ℕ} : u ^ 3 < n ^ 3 ↔ u < n := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have : n ^ 3 ≤ u ^ 3 := Nat.pow_le_pow_left hle 3
    exact (not_lt_of_ge this) h
  · intro h
    exact Nat.pow_lt_pow_left h (by decide : (3 : ℕ) ≠ 0)

/-- Locked scale: medium index sets for Spreads sit at most at `n/4`. -/
theorem random3CNFMatchScale_eq (n : ℕ) :
    random3CNFMatchScale n = n / 4 :=
  rfl

/-- Medium upper end equals the matchability scale. -/
theorem medium_hi_eq_matchScale (n : ℕ) :
    random3CNFMatchScale n = n / 4 :=
  random3CNFMatchScale_eq n

/-- If `|U| < 2 |S|` then concentration on `U` witnesses SpreadsIndices failure
for that `S` (used by the union bound over pairs `(S,U)`). -/
theorem not_spreadsIndices_of_concentrated_small {n m : ℕ}
    {ω : EnsembleIndex n m} {r : ℕ} {S : Finset (Fin m)}
    {U : Finset (Fin n)}
    (hlo : r / 2 ≤ S.card) (hhi : S.card ≤ r)
    (hconc : supportConcentrated ω S U)
    (hU : U.card < 2 * S.card) :
    ¬ SpreadsIndices ω r := by
  intro hsp
  have hExp := hsp S hlo hhi
  have hle := indexSupport_card_le_of_concentrated hconc
  omega

/-! ## Spreads summed choose packaging (Cluster 20)

Finite packaging for Step 3: Fin valued supports, crude failure terms
`C(m,s) C(n,2s-1) (8 (2s-1)^3)^s (8 n^3)^{m-s}`, and the card comparison
bridge from a strict inequality against `|Ω|` to an inhabited
`SpreadsIndices` sample. The crude close at locked `m = 6 n`, `r = n / 4`
fails already at the informative minimum `n = 32` (certified obstruction
below); a tighter count or pin revision is required before
`exists_spreads_matchable_unsat_random3CNF` can land. -/

/-- Fin valued support of an index set (coordinates, not `ℕ` images). -/
def indexSupportFin {n m : ℕ} (ω : EnsembleIndex n m) (S : Finset (Fin m)) :
    Finset (Fin n) :=
  S.biUnion fun i =>
    insert (ω i).x (insert (ω i).y ({(ω i).z} : Finset (Fin n)))

/-- Every sample is concentrated on its own Fin support. -/
theorem supportConcentrated_indexSupportFin {n m : ℕ}
    (ω : EnsembleIndex n m) (S : Finset (Fin m)) :
    supportConcentrated ω S (indexSupportFin ω S) := by
  intro i hi
  refine ⟨?_, ?_, ?_⟩
  · exact mem_biUnion.mpr ⟨i, hi, mem_insert_self _ _⟩
  · exact mem_biUnion.mpr ⟨i, hi, mem_insert_of_mem (mem_insert_self _ _)⟩
  · exact mem_biUnion.mpr ⟨i, hi,
      mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))⟩

/-- `ℕ` index support is the `Fin.val` image of the Fin support. -/
theorem indexSupport_eq_image_indexSupportFin {n m : ℕ}
    (ω : EnsembleIndex n m) (S : Finset (Fin m)) :
    indexSupport ω S = (indexSupportFin ω S).image Fin.val := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, hv'⟩ := mem_biUnion.mp hv
    simp only [Oriented3Clause.support, mem_insert, mem_singleton] at hv'
    rcases hv' with hv' | hv' | hv' <;> subst hv'
    · exact mem_image.mpr ⟨(ω i).x,
        mem_biUnion.mpr ⟨i, hi, mem_insert_self _ _⟩, rfl⟩
    · exact mem_image.mpr ⟨(ω i).y,
        mem_biUnion.mpr ⟨i, hi, mem_insert_of_mem (mem_insert_self _ _)⟩, rfl⟩
    · exact mem_image.mpr ⟨(ω i).z,
        mem_biUnion.mpr ⟨i, hi,
          mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))⟩, rfl⟩
  · intro hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    obtain ⟨i, hi, hx'⟩ := mem_biUnion.mp hx
    refine mem_biUnion.mpr ⟨i, hi, ?_⟩
    simp only [mem_insert, mem_singleton] at hx'
    simp only [Oriented3Clause.support, mem_insert, mem_singleton]
    rcases hx' with hx' | hx' | hx' <;> simp [hx']

/-- Fin support cardinality matches the `ℕ` support cardinality. -/
theorem card_indexSupportFin {n m : ℕ}
    (ω : EnsembleIndex n m) (S : Finset (Fin m)) :
    (indexSupportFin ω S).card = (indexSupport ω S).card := by
  classical
  have himg := indexSupport_eq_image_indexSupportFin ω S
  have hinj : Set.InjOn Fin.val (indexSupportFin ω S : Set (Fin n)) := by
    intro a _ b _ h
    exact Fin.val_injective h
  rw [himg]
  exact (card_image_of_injOn hinj).symm

/-- SpreadsIndices failure yields a medium Fin concentrated witness. -/
theorem exists_concentrated_fin_of_not_spreadsIndices {n m : ℕ}
    {ω : EnsembleIndex n m} {r : ℕ} (h : ¬ SpreadsIndices ω r) :
    ∃ S : Finset (Fin m), ∃ U : Finset (Fin n),
      r / 2 ≤ S.card ∧ S.card ≤ r ∧ U.card < 2 * S.card ∧
        supportConcentrated ω S U := by
  obtain ⟨S, hlo, hhi, hcard⟩ := exists_concentrated_of_not_spreadsIndices h
  refine ⟨S, indexSupportFin ω S, hlo, hhi, ?_,
    supportConcentrated_indexSupportFin ω S⟩
  have hceq := card_indexSupportFin ω S
  omega

/-- If not every sample fails SpreadsIndices, some sample spreads. -/
theorem exists_spreadsIndices_of_univ_card_lt {n m r : ℕ}
    (h : Fintype.card { ω : EnsembleIndex n m // ¬ SpreadsIndices ω r } <
      Fintype.card (EnsembleIndex n m)) :
    ∃ ω : EnsembleIndex n m, SpreadsIndices ω r := by
  classical
  by_contra hnone
  have hall : ∀ ω : EnsembleIndex n m, ¬ SpreadsIndices ω r := fun ω hsp =>
    hnone ⟨ω, hsp⟩
  have hEq :
      Fintype.card { ω : EnsembleIndex n m // ¬ SpreadsIndices ω r } =
        Fintype.card (EnsembleIndex n m) :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv hall)
  exact (Nat.ne_of_lt h) hEq

/-- Crude Spreads failure term at scale `s` (one `U` size `2s-1` slice). -/
def spreadsFailureTerm (n m s : ℕ) : ℕ :=
  Nat.choose m s * Nat.choose n (2 * s - 1) *
    (8 * (2 * s - 1) ^ 3) ^ s * (8 * n ^ 3) ^ (m - s)

/-- Cancel the free `(8 n^3)^{m-s}` factor in a term versus `|Ω|`. -/
theorem spreadsFailureTerm_lt_ensemble_iff {n m s : ℕ}
    (hpos : 0 < 8 * n ^ 3) (_hle : s ≤ m) :
    spreadsFailureTerm n m s < (8 * n ^ 3) ^ m ↔
      Nat.choose m s * Nat.choose n (2 * s - 1) * (8 * (2 * s - 1) ^ 3) ^ s <
        (8 * n ^ 3) ^ s := by
  unfold spreadsFailureTerm
  have hm : (8 * n ^ 3) ^ m =
      (8 * n ^ 3) ^ s * (8 * n ^ 3) ^ (m - s) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  constructor
  · intro h
    rw [hm] at h
    exact Nat.lt_of_mul_lt_mul_right h
  · intro h
    rw [hm]
    exact Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos hpos)

/-- Cancel the common `8^s` after the ensemble reduction. -/
theorem spreadsFailureTerm_core_lt_iff {n s : ℕ} (_hs : 0 < s) :
    Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
        (8 * (2 * s - 1) ^ 3) ^ s < (8 * n ^ 3) ^ s ↔
      Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
        (2 * s - 1) ^ (3 * s) < n ^ (3 * s) := by
  have h8pos : 0 < (8 : ℕ) := by decide
  have hL :
      (8 * (2 * s - 1) ^ 3) ^ s = 8 ^ s * (2 * s - 1) ^ (3 * s) := by
    rw [Nat.mul_pow, ← Nat.pow_mul]
  have hR : (8 * n ^ 3) ^ s = 8 ^ s * n ^ (3 * s) := by
    rw [Nat.mul_pow, ← Nat.pow_mul]
  constructor
  · intro h
    rw [hL, hR] at h
    have hre :
        Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
            (8 ^ s * (2 * s - 1) ^ (3 * s)) =
          (Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
            (2 * s - 1) ^ (3 * s)) * 8 ^ s := by
      ring
    have hre2 : 8 ^ s * n ^ (3 * s) = n ^ (3 * s) * 8 ^ s := by ring
    rw [hre, hre2] at h
    exact Nat.lt_of_mul_lt_mul_right h
  · intro h
    rw [hL, hR]
    have hmul :
        (Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
            (2 * s - 1) ^ (3 * s)) * 8 ^ s <
          n ^ (3 * s) * 8 ^ s :=
      Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos h8pos)
    have hre :
        Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
            (8 ^ s * (2 * s - 1) ^ (3 * s)) =
          (Nat.choose (6 * n) s * Nat.choose n (2 * s - 1) *
            (2 * s - 1) ^ (3 * s)) * 8 ^ s := by
      ring
    have hre2 : 8 ^ s * n ^ (3 * s) = n ^ (3 * s) * 8 ^ s := by ring
    rw [hre, hre2]
    exact hmul

/-- Building block: `32^2 < 15^3` (3375 vs 1024). -/
theorem thirty_two_pow_two_lt_fifteen_pow_three : (32 : ℕ) ^ 2 < 15 ^ 3 := by
  decide

/-- Raise the previous inequality to the 8th power: `32^16 < 15^24`. -/
theorem thirty_two_pow_sixteen_lt_fifteen_pow_twenty_four :
    (32 : ℕ) ^ 16 < 15 ^ 24 := by
  have h := thirty_two_pow_two_lt_fifteen_pow_three
  have hpow : ((32 : ℕ) ^ 2) ^ 8 < (15 ^ 3) ^ 8 :=
    Nat.pow_lt_pow_left h (by decide : (8 : ℕ) ≠ 0)
  have heq1 : ((32 : ℕ) ^ 2) ^ 8 = 32 ^ 16 := by
    rw [← Nat.pow_mul]
  have heq2 : (15 ^ 3) ^ 8 = 15 ^ 24 := by
    rw [← Nat.pow_mul]
  rwa [heq1, heq2] at hpow

/-- Hence `32^24 ≤ 15^24 * 32^8`. -/
theorem thirty_two_pow_twenty_four_le_fifteen_pow_mul_thirty_two_pow :
    (32 : ℕ) ^ 24 ≤ 15 ^ 24 * 32 ^ 8 := by
  have hlt := thirty_two_pow_sixteen_lt_fifteen_pow_twenty_four
  have hsplit : (32 : ℕ) ^ 24 = 32 ^ 16 * 32 ^ 8 := by
    rw [← Nat.pow_add]
  rw [hsplit]
  exact Nat.mul_le_mul_right _ (le_of_lt hlt)

/-- `Nat.factorial 8 ≤ 5^8`, used to lower-bound `Nat.choose 192 8`. -/
theorem eight_factorial_le_five_pow_eight : Nat.factorial 8 ≤ 5 ^ 8 := by
  decide

/-- `32 * 5 ≤ 185`, so `32^8 * 5^8 ≤ 185^8`. -/
theorem thirty_two_mul_five_le_one_eighty_five : (32 : ℕ) * 5 ≤ 185 := by
  decide

/-- Descending product lower bound: each of the eight factors is at least 185. -/
theorem descFactorial_one_ninety_two_eight_ge :
    (185 : ℕ) ^ 8 ≤ Nat.descFactorial 192 8 := by
  have h :
      Nat.descFactorial 192 8 =
        185 * (186 * (187 * (188 * (189 * (190 * (191 * 192)))))) := by
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
  rw [h]
  have h186 : (185 : ℕ) ≤ 186 := by decide
  have h187 : (185 : ℕ) ≤ 187 := by decide
  have h188 : (185 : ℕ) ≤ 188 := by decide
  have h189 : (185 : ℕ) ≤ 189 := by decide
  have h190 : (185 : ℕ) ≤ 190 := by decide
  have h191 : (185 : ℕ) ≤ 191 := by decide
  have h192 : (185 : ℕ) ≤ 192 := by decide
  calc
    (185 : ℕ) ^ 8
        = 185 * (185 * (185 * (185 * (185 * (185 * (185 * 185)))))) := by
          ring
    _ ≤ 185 * (186 * (187 * (188 * (189 * (190 * (191 * 192)))))) := by
      refine Nat.mul_le_mul le_rfl (Nat.mul_le_mul h186
        (Nat.mul_le_mul h187 (Nat.mul_le_mul h188
          (Nat.mul_le_mul h189 (Nat.mul_le_mul h190
            (Nat.mul_le_mul h191 h192))))))

/-- `32^8 ≤ Nat.choose 192 8`. -/
theorem choose_one_ninety_two_eight_ge_thirty_two_pow_eight :
    (32 : ℕ) ^ 8 ≤ Nat.choose 192 8 := by
  have hfac := eight_factorial_le_five_pow_eight
  have hbase := thirty_two_mul_five_le_one_eighty_five
  have h185 : (32 : ℕ) ^ 8 * 5 ^ 8 ≤ 185 ^ 8 := by
    simpa [Nat.mul_pow] using Nat.pow_le_pow_left hbase 8
  have hdesc := descFactorial_one_ninety_two_eight_ge
  have hchoos :
      Nat.choose 192 8 = Nat.descFactorial 192 8 / Nat.factorial 8 :=
    Nat.choose_eq_descFactorial_div_factorial 192 8
  have hmul : (32 : ℕ) ^ 8 * Nat.factorial 8 ≤ Nat.descFactorial 192 8 := by
    refine le_trans ?_ hdesc
    exact le_trans (Nat.mul_le_mul_left _ hfac) h185
  rw [hchoos]
  exact (Nat.le_div_iff_mul_le (Nat.factorial_pos 8)).2 hmul

/-- `1 ≤ Nat.choose 32 15`. -/
theorem choose_thirty_two_fifteen_pos : 1 ≤ Nat.choose 32 15 :=
  Nat.choose_pos (by decide : 15 ≤ 32)

/-- Honest obstruction (positive form): at locked `n = 32`, `s = 8`, the
crude cancelled term is at least `32^{24}`, so it is not strictly smaller. -/
theorem spreads_crude_core_ge_at_thirty_two :
    (32 : ℕ) ^ 24 ≤
      Nat.choose (6 * 32) 8 * Nat.choose 32 15 * (15 : ℕ) ^ 24 := by
  have h6 : (6 * 32 : ℕ) = 192 := by decide
  rw [h6]
  have hch := choose_one_ninety_two_eight_ge_thirty_two_pow_eight
  have hpos := choose_thirty_two_fifteen_pos
  have hpow := thirty_two_pow_twenty_four_le_fifteen_pow_mul_thirty_two_pow
  refine le_trans hpow ?_
  have hleft :
      (15 : ℕ) ^ 24 * 32 ^ 8 ≤ (15 : ℕ) ^ 24 * Nat.choose 192 8 :=
    Nat.mul_le_mul_left _ hch
  refine le_trans hleft ?_
  have hswap :
      (15 : ℕ) ^ 24 * Nat.choose 192 8 =
        Nat.choose 192 8 * (15 : ℕ) ^ 24 :=
    Nat.mul_comm _ _
  rw [hswap, mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpos)

/-- Negation form of the same obstruction (feeds the cancelled-term close). -/
theorem spreads_crude_core_not_lt_at_thirty_two :
    ¬ (Nat.choose (6 * 32) 8 * Nat.choose 32 15 * (15 : ℕ) ^ 24 <
        (32 : ℕ) ^ 24) :=
  not_lt_of_ge spreads_crude_core_ge_at_thirty_two

/-- Same obstruction before cancelling `8^s`, reduced by power algebra. -/
theorem spreads_crude_term_not_lt_eight_pow_at_thirty_two :
    ¬ (Nat.choose (6 * 32) 8 * Nat.choose 32 15 *
        (8 * 15 ^ 3) ^ 8 < (8 * 32 ^ 3) ^ 8) := by
  intro hlt
  have hL : (8 * 15 ^ 3) ^ 8 = 8 ^ 8 * (15 : ℕ) ^ 24 := by
    rw [Nat.mul_pow, ← Nat.pow_mul]
  have hR : (8 * 32 ^ 3) ^ 8 = 8 ^ 8 * (32 : ℕ) ^ 24 := by
    rw [Nat.mul_pow, ← Nat.pow_mul]
  rw [hL, hR] at hlt
  have hre :
      Nat.choose (6 * 32) 8 * Nat.choose 32 15 * (8 ^ 8 * (15 : ℕ) ^ 24) =
        (Nat.choose (6 * 32) 8 * Nat.choose 32 15 * (15 : ℕ) ^ 24) * 8 ^ 8 := by
    ring
  have hre2 : 8 ^ 8 * (32 : ℕ) ^ 24 = (32 : ℕ) ^ 24 * 8 ^ 8 := by ring
  rw [hre, hre2] at hlt
  have hcore :
      Nat.choose (6 * 32) 8 * Nat.choose 32 15 * (15 : ℕ) ^ 24 <
        (32 : ℕ) ^ 24 :=
    Nat.lt_of_mul_lt_mul_right hlt
  exact spreads_crude_core_not_lt_at_thirty_two hcore

/-- Medium scale at `n = 32` is `r = 8`. -/
theorem random3CNFMatchScale_thirty_two :
    random3CNFMatchScale 32 = 8 :=
  rfl

/-- Clause count at `n = 32` is `m = 192`. -/
theorem random3CNFClauseCount_thirty_two :
    random3CNFClauseCount 32 = 192 :=
  rfl

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
satisfiability and non informative floor, plus `SpreadsSupports`.

Cycle 2026-08-10 (cubic handshaking): certified
`handshaking_touching_of_regular3` (`2|touching|=3|S|+|∂S|`),
`spreads_starCNF_of_expansion`, and `spreads_heawoodStarCNF_five`.

Cycle 2026-08-11 (changed approach: SpreadsSupports first): certified matching
triple `SpreadsSupports` at informative `r = 8`, polarity independent
`clauseSupport_parityForbidClause`, `starClauseWith` or `starCNFWith`, and
`spreadsSupports_of_spreads`. Remaining for `exists_cs_clause_expanding_3cnf`:
inhabit a CNF on an informative SpreadsSupports system with matchable unsat
polarity (disjoint matchings alone are satisfiable clausewise), or a random
method lift from the certified set system witness.

Cycle 2026-08-11 (overlapping path): certified `loosePathSupports` SpreadsSupports
at informative `r = 8` with genuine adjacent overlaps, polarity encoding
`triplePolarityClause` or `cnfOfSupports`, matching polarity satisfiability
obstruction, and all-true path satisfiability. Overlap plus SpreadsSupports is
therefore inhabited; matchable unsat polarity (or probabilistic lift) remains.

Cycle 2026-08-11 (probabilistic scaffolding): accepted ensemble and packaging;
Frontier `exists_spreads_matchable_unsat_random3CNF` holds the counting gap.

Cycle 2026-08-11 (unsat first moment): accepted Nat bounds
`seven_pow_six_lt_two_pow_seventeen`, `two_pow_mul_seven_pow_lt_eight_pow`,
`exists_unsat_random3CNF`.

Cycle 2026-08-11 (Spreads and matchability scaffolding): accepted support
concentration fibers, `SpreadsIndices` lift, and matchability extraction from
large minimally unsat cores. Remaining: summed union bound inequalities.

Cycle 2026-08-11 (summed choose packaging): accepted `indexSupportFin`,
failure term algebra, card comparison bridge, and obstruction
`spreads_crude_core_not_lt_at_thirty_two` showing the crude close fails at
locked `n = 32`. Remaining: tighter Spreads count or pin revision, then
matchability, then package `exists_spreads_matchable_unsat_random3CNF`. -/

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
accepted route: `Spreads F (n/4) 2` plus `hasCSClauseExpansion_one_of_spreads_two`,
via packaging `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` once
`exists_spreads_matchable_unsat_random3CNF` lands. Probabilistic counting remains
open (sorry honest). -/
theorem exists_cs_clause_expanding_3cnf :
    ∀ N : ℕ, ∃ (n : ℕ) (F : CNF) (r α : ℕ),
      N ≤ n ∧ (cnfVars F).card = n ∧ cnfWidth F ≤ 3 ∧
        α = 1 ∧ r = n / 4 ∧
          IsCSMatchable F r ∧ HasCSClauseExpansion F r α ∧
            ¬ Satisfiable F ∧ cnfWidth F < csClauseWidthFloor r α := by
  sorry

/-- Random 3-CNF existence at locked density `m = 6 n` and scale `r = n / 4`.
Feeds the accepted packaging lemma once the three union bounds are formalized. -/
theorem exists_spreads_matchable_unsat_random3CNF :
    ∀ N : ℕ, ∃ (n : ℕ) (ω : EnsembleIndex n (random3CNFClauseCount n)),
      let F := random3CNF n (random3CNFClauseCount n) ω
      let r := random3CNFMatchScale n
      max N 32 ≤ n ∧ (cnfVars F).card = n ∧ cnfWidth F ≤ 3 ∧
        Spreads F r 2 ∧ IsCSMatchable F r ∧ ¬ Satisfiable F ∧
          cnfWidth F < csClauseWidthFloor r 1 := by
  sorry

end CSExpansionFrontier

end SATurday.ProofComplexity
