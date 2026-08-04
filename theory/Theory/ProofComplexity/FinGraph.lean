import Theory.ProofComplexity.Resolution
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite Graphs and Edge Expansion (Ladder Rung R2, item 2 cluster 1)

Lightweight undirected graphs on `Fin n` for the expander Tseitin width machine.
Pinned API from docs/ladder/rungs/r2-width-machinery.md: `FinEdge`, `FinGraph`,
`incident`, `degree`, `IsRegular`, `edgeBoundary`, `HasExpansion`, elementary
lemmas, and the explicit Petersen graph.

`petersenGraph_expansion` is deferred (finite but heavy enumeration; not claimed
here). This cluster certifies the construction, edge count, and 3-regularity.

LOG: R2 FinGraph API and Petersen construction
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Edges and graphs on `Fin n` -/

/-- An unordered edge on vertex set `Fin n`, stored as an ordered pair with the
lesser endpoint first. -/
def FinEdge (n : ℕ) := { e : Fin n × Fin n // e.1 < e.2 }

instance (n : ℕ) : DecidableEq (FinEdge n) := Subtype.instDecidableEq

/-- A simple undirected graph on `Fin n` is a finite set of edges. -/
abbrev FinGraph (n : ℕ) := Finset (FinEdge n)

/-- Build an edge from two naturals with the lesser first. -/
def finEdgeOf {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i < j) :
    FinEdge n :=
  ⟨(⟨i, hi⟩, ⟨j, hj⟩), hij⟩

/-- Edges of `G` that contain vertex `v`. -/
def incident {n : ℕ} (G : FinGraph n) (v : Fin n) : Finset (FinEdge n) :=
  G.filter fun e => e.val.1 = v ∨ e.val.2 = v

/-- Degree of `v` in `G`. -/
def degree {n : ℕ} (G : FinGraph n) (v : Fin n) : ℕ := (incident G v).card

/-- `G` is `d`-regular when every vertex has degree `d`. -/
def IsRegular {n : ℕ} (G : FinGraph n) (d : ℕ) : Prop :=
  ∀ v : Fin n, degree G v = d

/-- Cut edges of `S`: edges of `G` with exactly one endpoint in `S`. -/
def edgeBoundary {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) :
    Finset (FinEdge n) :=
  G.filter fun e =>
    (e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.1 ∉ S ∧ e.val.2 ∈ S)

/-- Integer edge expansion: every nonempty set with `2 * S.card ≤ n` has cut size
at least `α * S.card`. -/
def HasExpansion {n : ℕ} (G : FinGraph n) (α : ℕ) : Prop :=
  ∀ S : Finset (Fin n),
    S.Nonempty → 2 * S.card ≤ n → α * S.card ≤ (edgeBoundary G S).card

/-! ## Elementary lemmas -/

theorem mem_incident_iff {n : ℕ} {G : FinGraph n} {v : Fin n} {e : FinEdge n} :
    e ∈ incident G v ↔ e ∈ G ∧ (e.val.1 = v ∨ e.val.2 = v) := by
  simp [incident]

theorem incident_subset {n : ℕ} (G : FinGraph n) (v : Fin n) :
    incident G v ⊆ G :=
  filter_subset _ _

theorem mem_edgeBoundary_iff {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} :
    e ∈ edgeBoundary G S ↔
      e ∈ G ∧
        ((e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.1 ∉ S ∧ e.val.2 ∈ S)) := by
  simp [edgeBoundary]

theorem edgeBoundary_subset {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) :
    edgeBoundary G S ⊆ G :=
  filter_subset _ _

/-- The empty vertex set has empty cut. -/
theorem edgeBoundary_empty {n : ℕ} (G : FinGraph n) :
    edgeBoundary G (∅ : Finset (Fin n)) = ∅ := by
  ext e
  simp [edgeBoundary]

/-- The full vertex set has empty cut. -/
theorem edgeBoundary_univ {n : ℕ} (G : FinGraph n) :
    edgeBoundary G (univ : Finset (Fin n)) = ∅ := by
  ext e
  simp [edgeBoundary]

/-- Cut of `S` equals cut of its complement. -/
theorem edgeBoundary_sdiff_univ {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) :
    edgeBoundary G S = edgeBoundary G (univ \ S) := by
  ext e
  simp [edgeBoundary, mem_sdiff]
  tauto

/-- Endpoints of an edge are distinct. -/
theorem FinEdge.ne_endpoints {n : ℕ} (e : FinEdge n) : e.val.1 ≠ e.val.2 :=
  ne_of_lt e.property

/-- Singleton cut equals the star of that vertex. -/
theorem edgeBoundary_singleton {n : ℕ} (G : FinGraph n) (v : Fin n) :
    edgeBoundary G ({v} : Finset (Fin n)) = incident G v := by
  ext e
  simp only [mem_edgeBoundary_iff, mem_incident_iff, mem_singleton]
  constructor
  · rintro ⟨heG, hcut⟩
    refine ⟨heG, ?_⟩
    rcases hcut with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro ⟨heG, hinc⟩
    refine ⟨heG, ?_⟩
    rcases hinc with h1 | h2
    · have hne : e.val.2 ≠ v := by
        intro heq
        exact absurd (h1.trans heq.symm) e.ne_endpoints
      exact Or.inl ⟨h1, hne⟩
    · have hne : e.val.1 ≠ v := by
        intro heq
        exact absurd (heq.trans h2.symm) e.ne_endpoints
      exact Or.inr ⟨hne, h2⟩

/-- Positive expansion forces every degree at least `α` (singleton cuts). -/
theorem HasExpansion.degree_ge {n : ℕ} {G : FinGraph n} {α : ℕ}
    (h : HasExpansion G α) (hn : 2 ≤ n) (v : Fin n) : α ≤ degree G v := by
  have hS : ({v} : Finset (Fin n)).Nonempty := singleton_nonempty v
  have hcard : 2 * ({v} : Finset (Fin n)).card ≤ n := by simp [hn]
  have hbd := h ({v} : Finset (Fin n)) hS hcard
  simpa [edgeBoundary_singleton, card_singleton, mul_one] using hbd

/-! ## Petersen graph (outer 5-cycle, spokes, inner pentagram) -/

/-- Helper: edge on `Fin 10` from concrete naturals (proofs filled by `decide`). -/
private def pEdge (i j : ℕ) (hij : i < j := by decide) (hj : j < 10 := by decide) :
    FinEdge 10 :=
  finEdgeOf i j (lt_trans hij hj) hj hij

/-- The Petersen graph on 10 vertices as an explicit 15-edge set.
Outer cycle `0..4`, spokes `i -- i+5`, inner star `5-7-9-6-8-5`. -/
def petersenGraph : FinGraph 10 :=
  { pEdge 0 1, pEdge 1 2, pEdge 2 3, pEdge 3 4, pEdge 0 4,
    pEdge 0 5, pEdge 1 6, pEdge 2 7, pEdge 3 8, pEdge 4 9,
    pEdge 5 7, pEdge 7 9, pEdge 6 9, pEdge 6 8, pEdge 5 8 }

/-- Petersen has exactly 15 edges. -/
theorem petersenGraph_card : petersenGraph.card = 15 := by decide

/-- Petersen is 3-regular (finite check over `Fin 10`). -/
theorem petersenGraph_regular : IsRegular petersenGraph 3 := by
  intro v
  fin_cases v <;> decide

end SATurday.ProofComplexity
