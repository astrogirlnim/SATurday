import Theory.ProofComplexity.FinGraph
import Theory.ProofComplexity.Width

/-!
# Tseitin CNF on FinGraphs (Ladder Rung R2, item 2 cluster 2 start)

Charge, edge variables, and the Tseitin CNF construction over the FinGraph API.
Unsatisfiability (`tseitinCNF_unsat`) and the expander width lower bound are
later clusters; this module ships the syntax pinned in
docs/ladder/rungs/r2-width-machinery.md.

Encoding: each edge `e` gets variable `edgeVar e`. At vertex `v` of degree `d`,
the `2^(d-1)` parity clauses force the XOR of incident edge variables to equal
the charge `χ v`.

LOG: R2 Tseitin CNF construction
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Charge -/

/-- Boolean charge on vertices of `Fin n`. -/
abbrev Charge (n : ℕ) := Fin n → Bool

/-- Odd total charge: an odd number of vertices carry `true`. -/
def oddCharge {n : ℕ} (χ : Charge n) : Prop :=
  ((univ : Finset (Fin n)).filter fun v => χ v = true).card % 2 = 1

/-- Single-vertex odd charge: `true` only at `v`. -/
def oddCharge_single (n : ℕ) (v : Fin n) : Charge n :=
  fun w => decide (w = v)

/-- The single-vertex charge is odd (non vacuity seed for Tseitin). -/
theorem oddCharge_single_odd (n : ℕ) (v : Fin n) :
    oddCharge (oddCharge_single n v) := by
  -- The filter of true charges is the singleton `{v}`, card 1, odd.
  have hfilter :
      ((univ : Finset (Fin n)).filter fun w => oddCharge_single n v w = true) =
        ({v} : Finset (Fin n)) := by
    ext w
    simp [oddCharge_single]
  simp [oddCharge, hfilter]

/-! ## Edge variables and parity clauses -/

/-- Canonical injection from edges on `Fin n` into variable indices. -/
def edgeVar {n : ℕ} (e : FinEdge n) : ℕ := e.val.1.val * n + e.val.2.val

/-- Distinct edges receive distinct variable indices when `n > 0`. -/
theorem edgeVar_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (@edgeVar n) := by
  intro e1 e2 heq
  rcases e1 with ⟨⟨i1, j1⟩, _⟩
  rcases e2 with ⟨⟨i2, j2⟩, _⟩
  simp only [edgeVar] at heq
  have hj1 : j1.val < n := j1.isLt
  have hj2 : j2.val < n := j2.isLt
  -- Rewrite to `n * i + j` form for the standard digit lemmas.
  have heq' : n * i1.val + j1.val = n * i2.val + j2.val := by
    simpa [Nat.mul_comm] using heq
  have hdiv1 : (n * i1.val + j1.val) / n = i1.val := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj1, add_zero]
  have hdiv2 : (n * i2.val + j2.val) / n = i2.val := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj2, add_zero]
  have hmod1 : (n * i1.val + j1.val) % n = j1.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj1]
  have hmod2 : (n * i2.val + j2.val) % n = j2.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj2]
  have hi : i1.val = i2.val := by rw [← hdiv1, ← hdiv2, heq']
  have hj : j1.val = j2.val := by rw [← hmod1, ← hmod2, heq']
  refine Subtype.ext ?_
  exact Prod.ext (Fin.ext hi) (Fin.ext hj)

/-- Clause forbidding one assignment of incident edge variables: for support `S`,
each edge in `S` gets a negative literal and each edge outside `S` a positive one. -/
def parityForbidClause {n : ℕ} (I : Finset (FinEdge n)) (S : Finset (FinEdge n)) :
    Clause :=
  I.image fun e => (⟨edgeVar e, decide (e ∉ S)⟩ : Literal)

/-- Vertex parity CNF: all forbidding clauses for assignments whose XOR differs
from the charge at `v`. -/
def vertexParityClauses {n : ℕ} (G : FinGraph n) (χ : Charge n) (v : Fin n) :
    CNF :=
  let I := incident G v
  (I.powerset.filter fun S => decide (S.card % 2 = 1) ≠ χ v).image
    fun S => parityForbidClause I S

/-- Tseitin CNF: union of vertex parity constraints over all vertices. -/
def tseitinCNF {n : ℕ} (G : FinGraph n) (χ : Charge n) : CNF :=
  (univ : Finset (Fin n)).biUnion fun v => vertexParityClauses G χ v

/-- Every hypothesis clause of the Tseitin CNF comes from some vertex. -/
theorem mem_tseitinCNF_iff {n : ℕ} {G : FinGraph n} {χ : Charge n} {C : Clause} :
    C ∈ tseitinCNF G χ ↔
      ∃ v : Fin n, C ∈ vertexParityClauses G χ v := by
  simp [tseitinCNF]

/-- Variables of a forbidding clause are edge variables of the incident star. -/
theorem clauseVars_parityForbidClause_subset {n : ℕ}
    (I S : Finset (FinEdge n)) :
    clauseVars (parityForbidClause I S) ⊆ I.image edgeVar := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
  obtain ⟨e, he, rfl⟩ := mem_image.mp hl
  exact mem_image.mpr ⟨e, he, rfl⟩

end SATurday.ProofComplexity
