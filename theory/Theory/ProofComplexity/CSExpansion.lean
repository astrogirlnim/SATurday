import Theory.ProofComplexity.Width
import Theory.ProofComplexity.SizeWidth

/-!
# Chvatal–Szemeredi expansion for k-CNF (Ladder Rung R2, item 2)

Pinned API from docs/ladder/rungs/r2-width-machinery.md: `boundaryClauses`,
`HasCSExpansion`, `csWidthDiv`, scaffolding toward
`cs_expansion_width_lower_bound`. Reuses certified `cnfWidth` / `cnfVars` and
the BSW size machine from SizeWidth.lean.

This first cluster freezes the discrete expansion hypothesis and elementary
boundary lemmas. The full width lower bound (complex growth with clause
boundary substituted for graph cuts) is the next formalize target; existence
`exists_cs_expanding_3cnf` remains a hard probabilistic gap.

LOG: R2 CSExpansion API and elementary boundary lemmas
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

end SATurday.ProofComplexity
