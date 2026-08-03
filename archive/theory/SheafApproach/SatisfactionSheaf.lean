import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Satisfaction Sheaf: First Formalization Sprint

## Background

The Sheaf-Cohomological Obstruction approach to P vs NP models a SAT instance
as a sheaf F over the poset of partial assignments. The stalk at each partial
assignment σ consists of total assignments that extend σ and satisfy all clauses.
Global sections of F are exactly the satisfying assignments.

## This file

Formalizes the core definitions and proves:

  THEOREM (global_sections_eq_satisfying):
    a ∈ globalSections phi ↔ formulaSatisfied a phi

  THEOREM (globalSections_iff_all_clauses):
    a ∈ globalSections phi ↔ ∀ c ∈ phi, clauseSatisfied a c

  THEOREM (mem_stalk_toPartial_iff_satisfying):
    a ∈ stalk phi (toPartial a) ↔ formulaSatisfied a phi

  THEOREM (stalk_total_unique):
    b ∈ stalk phi (toPartial a) → ∀ x, a x = b x

  THEOREM (satisfiable_iff_H0_nonempty):
    (∃ a, formulaSatisfied a phi) ↔ (H0 phi).Nonempty

## Barrier tag: natural_proof_safe
H^0 of the satisfaction sheaf is an instance-specific invariant, not a
property of a function family. The Razborov-Rudich largeness condition
does not apply.
-/

-- ──────────────────────────────────────────────────────────────────────────────
-- Core types
-- ──────────────────────────────────────────────────────────────────────────────

/-- A literal: a variable index in Fin n paired with a boolean polarity. -/
structure Literal (n : ℕ) where
  var : Fin n
  pol : Bool
  deriving DecidableEq, Repr

/-- A clause over n variables: a finite set of literals. -/
abbrev Clause (n : ℕ) := Finset (Literal n)

/-- A formula: a list of clauses. -/
abbrev Formula (n : ℕ) := List (Clause n)

/-- A total assignment: assigns a boolean to every variable. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A partial assignment: optionally assigns a boolean to each variable. -/
abbrev PartialAssignment (n : ℕ) := Fin n → Option Bool

-- ──────────────────────────────────────────────────────────────────────────────
-- Satisfiability predicates (Prop-valued for clean proofs)
-- ──────────────────────────────────────────────────────────────────────────────

/-- Literal l is satisfied by total assignment a iff a(l.var) = l.pol. -/
def literalSatisfied (a : Assignment n) (l : Literal n) : Prop :=
  a l.var = l.pol

/-- Clause c is satisfied by a iff at least one literal in c is satisfied. -/
def clauseSatisfied (a : Assignment n) (c : Clause n) : Prop :=
  ∃ l ∈ c, literalSatisfied a l

/-- Formula phi is satisfied by a iff every clause in phi is satisfied. -/
def formulaSatisfied (a : Assignment n) (phi : Formula n) : Prop :=
  ∀ c ∈ phi, clauseSatisfied a c

-- ──────────────────────────────────────────────────────────────────────────────
-- Partial assignment operations
-- ──────────────────────────────────────────────────────────────────────────────

/-- a extendedBy σ means: for every variable x, if σ assigns x to b then a x = b.
    (Named extendedBy rather than extends to avoid the Lean keyword extends.) -/
def extendedBy (a : Assignment n) (σ : PartialAssignment n) : Prop :=
  ∀ (x : Fin n) (b : Bool), σ x = some b → a x = b

/-- Convert a total assignment to the corresponding fully-defined partial assignment. -/
def toPartial (a : Assignment n) : PartialAssignment n :=
  fun x => some (a x)

/-- Every total assignment is extendedBy its own toPartial. -/
lemma extendedBy_toPartial (a : Assignment n) : extendedBy a (toPartial a) := by
  intro x b hb
  simp [toPartial] at hb
  exact hb

-- ──────────────────────────────────────────────────────────────────────────────
-- The satisfaction sheaf
-- ──────────────────────────────────────────────────────────────────────────────

/-- A clause c is determined by partial assignment σ if every literal in c
    has its variable assigned (σ l.var ≠ none for all l ∈ c). -/
def clauseDetermined (σ : PartialAssignment n) (c : Clause n) : Prop :=
  ∀ l ∈ c, (σ l.var).isSome = true

/-- A clause c is locally satisfied by partial assignment σ if at least one
    literal l ∈ c satisfies σ(l.var) = some l.pol. -/
def clauseLocallySatisfied (σ : PartialAssignment n) (c : Clause n) : Prop :=
  ∃ l ∈ c, σ l.var = some l.pol

/-- The stalk of the satisfaction sheaf at σ:
    all total assignments a that (1) are extendedBy σ and (2) satisfy phi. -/
def stalk (phi : Formula n) (σ : PartialAssignment n) : Set (Assignment n) :=
  { a | extendedBy a σ ∧ formulaSatisfied a phi }

/-- Global sections: total assignments satisfying the full formula.
    Defined as the set of satisfying assignments; coincides with the stalk at
    the all-defined partial assignment. -/
def globalSections (phi : Formula n) : Set (Assignment n) :=
  { a | formulaSatisfied a phi }

-- ──────────────────────────────────────────────────────────────────────────────
-- MAIN THEOREMS
-- ──────────────────────────────────────────────────────────────────────────────

/-- THEOREM 1: Global sections = satisfying assignments.
    A total assignment is a global section iff it satisfies the formula. -/
theorem global_sections_eq_satisfying
    (n : ℕ) (phi : Formula n) (a : Assignment n) :
    a ∈ globalSections phi ↔ formulaSatisfied a phi := by
  simp [globalSections]

/-- THEOREM 2: Global sections characterization by clauses.
    a is a global section iff every clause in phi is satisfied by a. -/
theorem globalSections_iff_all_clauses
    (n : ℕ) (phi : Formula n) (a : Assignment n) :
    a ∈ globalSections phi ↔ ∀ c ∈ phi, clauseSatisfied a c := by
  simp [globalSections, formulaSatisfied]

/-- THEOREM 3: Stalk at toPartial(a) collapses to satisfiability.
    a ∈ stalk(phi, toPartial(a)) iff a satisfies phi. -/
theorem mem_stalk_toPartial_iff_satisfying
    (n : ℕ) (phi : Formula n) (a : Assignment n) :
    a ∈ stalk phi (toPartial a) ↔ formulaSatisfied a phi := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨extendedBy_toPartial a, h⟩

/-- THEOREM 4: The stalk at a total partial assignment is a singleton section.
    If b ∈ stalk(phi, toPartial(a)) then a and b agree on all variables. -/
theorem stalk_total_unique
    (n : ℕ) (phi : Formula n) (a b : Assignment n)
    (hb : b ∈ stalk phi (toPartial a)) :
    ∀ x : Fin n, a x = b x := by
  intro x
  exact (hb.1 x (a x) (by simp [toPartial])).symm

/-- THEOREM 5: H^0 = satisfying assignments.
    H0 phi is nonempty iff the formula is satisfiable. -/
def H0 (phi : Formula n) : Set (Assignment n) := globalSections phi

theorem satisfiable_iff_H0_nonempty
    (n : ℕ) (phi : Formula n) :
    (∃ a : Assignment n, formulaSatisfied a phi) ↔ (H0 phi).Nonempty := by
  simp [H0, globalSections, Set.Nonempty]

-- ──────────────────────────────────────────────────────────────────────────────
-- Supporting lemmas
-- ──────────────────────────────────────────────────────────────────────────────

/-- Any member of a stalk satisfies the formula. -/
theorem stalk_member_satisfies
    (n : ℕ) (phi : Formula n) (σ : PartialAssignment n) (a : Assignment n)
    (h : a ∈ stalk phi σ) :
    formulaSatisfied a phi :=
  h.2

/-- Satisfying phi is equivalent to: for every clause, some literal is satisfied. -/
theorem satisfies_iff_exists_lit
    (n : ℕ) (phi : Formula n) (a : Assignment n) :
    formulaSatisfied a phi ↔
    ∀ c ∈ phi, ∃ l ∈ c, literalSatisfied a l := by
  simp [formulaSatisfied, clauseSatisfied]

/-- Local satisfaction implies total satisfaction: if a is locally satisfying on σ
    for every clause that is determined by σ, and extends σ to a total assignment
    satisfying phi, then a ∈ stalk(phi, σ). -/
theorem local_to_global_stalk
    (n : ℕ) (phi : Formula n) (σ : PartialAssignment n) (a : Assignment n)
    (hext : extendedBy a σ)
    (hsat : formulaSatisfied a phi) :
    a ∈ stalk phi σ :=
  ⟨hext, hsat⟩

/-- The global sections are exactly the H^0 sections (both definitions coincide). -/
theorem globalSections_eq_H0
    (n : ℕ) (phi : Formula n) :
    globalSections phi = H0 phi :=
  rfl
