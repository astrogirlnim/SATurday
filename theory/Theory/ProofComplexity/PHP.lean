import Theory.ProofComplexity.Resolution

/-!
# The Pigeonhole Family and the R1 Target (Haken Lower Bound)

This module defines the propositional pigeonhole family PHP(n+1, n) as a CNF
over the R0 syntax and proves it unsatisfiable. The unsatisfiability proof is
the recorded non-vacuity witness demanded by the proof standards: together with
refutational completeness (R0), it shows resolution refutations of PHP(n+1, n)
exist, so the R1 lower bound quantifies over a nonempty set of derivations.

The exponential R1 size lower bound is certified in
`MonotoneCalculus.lean` as `php_resolution_size_lower_bound` (honest rate
supported by the current width and kill lemmas). The stronger paper constant
`2^(n/20)` is not claimed; recovering it is optional future work, not a
blocker for R1 certification.

Encoding: pigeon i in Fin (n+1), hole j in Fin n, variable index i * n + j.
Clauses: every pigeon sits somewhere; no two pigeons share a hole.

LOG: R1 pigeonhole family module
-/

namespace SATurday.ProofComplexity

/-- Variable index for "pigeon i sits in hole j". -/
def pvar (n : ℕ) (i : Fin (n + 1)) (j : Fin n) : ℕ := i.val * n + j.val

/-- The clause "pigeon i sits in some hole": all positive literals over holes. -/
def pigeonClause (n : ℕ) (i : Fin (n + 1)) : Clause :=
  (Finset.univ : Finset (Fin n)).image fun j => ⟨pvar n i j, true⟩

/-- All pigeon clauses. -/
def pigeonClauses (n : ℕ) : CNF :=
  (Finset.univ : Finset (Fin (n + 1))).image fun i => pigeonClause n i

/-- All hole clauses "pigeons i < i' do not share hole j": two negative literals. -/
def holeClauses (n : ℕ) : CNF :=
  (Finset.univ : Finset (Fin n)).biUnion fun j =>
    (Finset.univ : Finset (Fin (n + 1))).biUnion fun i =>
      ((Finset.univ : Finset (Fin (n + 1))).filter fun i' => i < i').image fun i' =>
        ({⟨pvar n i j, false⟩, ⟨pvar n i' j, false⟩} : Clause)

/-- The pigeonhole CNF: n+1 pigeons, n holes. -/
def phpCNF (n : ℕ) : CNF := pigeonClauses n ∪ holeClauses n

/-! ## Unsatisfiability (the non-vacuity witness) -/

/-- Under a satisfying assignment, pigeons choosing the same hole would violate
the hole clause for the smaller-index pair, so the chosen holes differ. -/
theorem no_shared_hole {n : ℕ} {a : Assignment} (ha : cnfSat a (phpCNF n))
    {f : Fin (n + 1) → Fin n} (hf : ∀ i, a (pvar n i (f i)) = true)
    {i i' : Fin (n + 1)} (hlt : i < i') : f i ≠ f i' := by
  intro heq
  -- The hole clause forbidding i and i' from sharing hole (f i) is in the CNF.
  have hclause : ({⟨pvar n i (f i), false⟩, ⟨pvar n i' (f i), false⟩} : Clause)
      ∈ phpCNF n := by
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_biUnion.mpr ⟨f i, Finset.mem_univ _, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr
      ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
  obtain ⟨l, hl, hla⟩ := ha _ hclause
  rcases Finset.mem_insert.mp hl with rfl | hl
  · -- The first negative literal contradicts pigeon i's positive choice.
    simp only [litSat] at hla
    rw [hf i] at hla
    exact Bool.noConfusion hla
  · -- The second contradicts pigeon i's choice transported along f i = f i'.
    rw [Finset.mem_singleton] at hl
    subst hl
    simp only [litSat] at hla
    have htrue := hf i'
    rw [← heq] at htrue
    rw [htrue] at hla
    exact Bool.noConfusion hla

/-- The hole-choice function of a satisfying assignment is injective. -/
theorem php_choice_injective {n : ℕ} {a : Assignment} (ha : cnfSat a (phpCNF n))
    {f : Fin (n + 1) → Fin n} (hf : ∀ i, a (pvar n i (f i)) = true) :
    Function.Injective f := by
  intro i i' heq
  by_contra hne
  rcases lt_trichotomy i i' with hlt | heqi | hlt
  · exact no_shared_hole ha hf hlt heq
  · exact hne heqi
  · exact no_shared_hole ha hf hlt heq.symm

/-- PHP(n+1, n) is unsatisfiable: a model would give an injection from n+1
pigeons into n holes, contradicting cardinality. This is the recorded
non-vacuity witness for the R1 lower bound. -/
theorem phpCNF_unsat (n : ℕ) : ¬Satisfiable (phpCNF n) := by
  rintro ⟨a, ha⟩
  -- Every pigeon clause is satisfied, so every pigeon has a chosen hole.
  have hex : ∀ i : Fin (n + 1), ∃ j : Fin n, a (pvar n i j) = true := by
    intro i
    have hcl : pigeonClause n i ∈ phpCNF n :=
      Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    obtain ⟨l, hl, hla⟩ := ha _ hcl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨j, hla⟩
  choose f hf using hex
  have hinj : Function.Injective f := php_choice_injective ha hf
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin, Fintype.card_fin] at hcard
  omega

/-- Corollary via R0 completeness: resolution refutations of PHP(n+1, n) exist.
This is the formal shape of the non-vacuity witness. -/
theorem phpCNF_refutable (n : ℕ) : Refutable (phpCNF n) :=
  resolution_complete (phpCNF_unsat n)

end SATurday.ProofComplexity
