import Theory.ProofComplexity.Resolution
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite Graphs and Edge Expansion (Ladder Rung R2, item 2 cluster 1)

Lightweight undirected graphs on `Fin n` for the expander Tseitin width machine.
Pinned API from docs/ladder/rungs/r2-width-machinery.md: `FinEdge`, `FinGraph`,
`incident`, `degree`, `IsRegular`, `edgeBoundary`, `HasExpansion`, elementary
lemmas, and the explicit Petersen graph.

Cluster 1b certifies `petersenGraph_expansion` at pinned alpha = 1. That factor
is honest and tight on this encoding (some half-size sets have cut ratio exactly
1; alpha = 2 is false).

LOG: R2 FinGraph API Petersen construction and expansion
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

/-! ## Walks, reachability, and expansion implies connectivity -/

/-- Adjacent vertices along an edge of `G`. -/
def FinGraph.Adj {n : ℕ} (G : FinGraph n) (u v : Fin n) : Prop :=
  ∃ e ∈ G, (e.val.1 = u ∧ e.val.2 = v) ∨ (e.val.1 = v ∧ e.val.2 = u)

/-- Undirected reachability in `G`. -/
def FinGraph.Reachable {n : ℕ} (G : FinGraph n) (u v : Fin n) : Prop :=
  Relation.ReflTransGen G.Adj u v

/-- Every pair of vertices is reachable. -/
def FinGraph.IsConnected {n : ℕ} (G : FinGraph n) : Prop :=
  ∀ u v : Fin n, G.Reachable u v

/-- Reachable component of a vertex. -/
noncomputable def FinGraph.component {n : ℕ} (G : FinGraph n) (u : Fin n) :
    Finset (Fin n) :=
  univ.filter fun v => G.Reachable u v

theorem FinGraph.mem_component_iff {n : ℕ} {G : FinGraph n} {u v : Fin n} :
    v ∈ G.component u ↔ G.Reachable u v := by
  simp [FinGraph.component]

theorem FinGraph.self_mem_component {n : ℕ} (G : FinGraph n) (u : Fin n) :
    u ∈ G.component u := by
  simp [FinGraph.mem_component_iff, FinGraph.Reachable, Relation.ReflTransGen.refl]

theorem FinGraph.component_nonempty {n : ℕ} (G : FinGraph n) (u : Fin n) :
    (G.component u).Nonempty :=
  ⟨u, G.self_mem_component u⟩

/-- No edge leaves a reachable component. -/
theorem FinGraph.edgeBoundary_component {n : ℕ} (G : FinGraph n) (u : Fin n) :
    edgeBoundary G (G.component u) = ∅ := by
  ext e
  simp only [mem_edgeBoundary_iff, Finset.notMem_empty, iff_false]
  rintro ⟨heG, hcut⟩
  have hadj : G.Adj e.val.1 e.val.2 := ⟨e, heG, Or.inl ⟨rfl, rfl⟩⟩
  have hadj' : G.Adj e.val.2 e.val.1 := ⟨e, heG, Or.inr ⟨rfl, rfl⟩⟩
  rcases hcut with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- e.1 in component, e.2 not: but adjacency extends reachability
    have r1 : G.Reachable u e.val.1 := (G.mem_component_iff).mp h1
    have r2 : G.Reachable u e.val.2 :=
      Relation.ReflTransGen.tail r1 hadj
    exact h2 ((G.mem_component_iff).mpr r2)
  · have r2 : G.Reachable u e.val.2 := (G.mem_component_iff).mp h2
    have r1 : G.Reachable u e.val.1 :=
      Relation.ReflTransGen.tail r2 hadj'
    exact h1 ((G.mem_component_iff).mpr r1)

/-- Positive expansion forbids a proper nonempty component with empty cut, so
`G` is connected whenever `α ≥ 1`. -/
theorem HasExpansion.isConnected {n : ℕ} {G : FinGraph n} {α : ℕ}
    (h : HasExpansion G α) (hα : 1 ≤ α) : G.IsConnected := by
  intro u v
  by_contra huv
  set S := G.component u with hSdef
  have hne : S.Nonempty := G.component_nonempty u
  have hbd : edgeBoundary G S = ∅ := G.edgeBoundary_component u
  have hvS : v ∉ S := by
    intro hv
    exact huv ((G.mem_component_iff).mp hv)
  have hSneUniv : S ≠ (univ : Finset (Fin n)) := by
    intro hSu
    exact hvS (hSu ▸ mem_univ v)
  by_cases hHalf : 2 * S.card ≤ n
  · have hge := h S hne hHalf
    rw [hbd, card_empty] at hge
    -- hge : α * S.card ≤ 0, with α ≥ 1 and S nonempty
    have hc : 1 ≤ S.card := Nat.succ_le_of_lt (card_pos.mpr hne)
    exact absurd hge (Nat.not_le.mpr (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hα) (lt_of_lt_of_le Nat.zero_lt_one hc)))
  · set T := (univ : Finset (Fin n)) \ S
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hTempty
      apply hSneUniv
      exact eq_univ_of_forall fun x => by
        by_contra hx
        have hxT : x ∈ T := mem_sdiff.mpr ⟨mem_univ x, hx⟩
        simp [hTempty] at hxT
    have hsum : S.card + T.card = n := by
      have hd : Disjoint S T := disjoint_sdiff
      have hu : S ∪ T = (univ : Finset (Fin n)) := by
        ext x; simp [T]
      calc
        S.card + T.card = (S ∪ T).card := (card_union_of_disjoint hd).symm
        _ = (univ : Finset (Fin n)).card := by rw [hu]
        _ = n := by simp
    have hTcard : 2 * T.card ≤ n := by omega
    have hbdT : edgeBoundary G T = ∅ := by
      rw [← edgeBoundary_sdiff_univ G S, hbd]
    have hge := h T hTne hTcard
    rw [hbdT, card_empty] at hge
    have hc : 1 ≤ T.card := Nat.succ_le_of_lt (card_pos.mpr hTne)
    exact absurd hge (Nat.not_le.mpr (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hα) (lt_of_lt_of_le Nat.zero_lt_one hc)))

/-! ## Adjacency edge choice (for Tseitin parity repairs) -/

/-- Choose an edge witnessing `G.Adj u v`. -/
noncomputable def FinGraph.adjEdge {n : ℕ} (G : FinGraph n) {u v : Fin n}
    (h : G.Adj u v) : FinEdge n :=
  Classical.choose h

theorem FinGraph.adjEdge_spec {n : ℕ} (G : FinGraph n) {u v : Fin n}
    (h : G.Adj u v) :
    G.adjEdge h ∈ G ∧
      ((G.adjEdge h).val.1 = u ∧ (G.adjEdge h).val.2 = v ∨
        (G.adjEdge h).val.1 = v ∧ (G.adjEdge h).val.2 = u) :=
  Classical.choose_spec h

theorem FinGraph.adjEdge_mem {n : ℕ} (G : FinGraph n) {u v : Fin n}
    (h : G.Adj u v) : G.adjEdge h ∈ G :=
  (G.adjEdge_spec h).1

/-- The chosen adjacency edge is incident to both endpoints. -/
theorem FinGraph.adjEdge_mem_incident {n : ℕ} (G : FinGraph n) {u v : Fin n}
    (h : G.Adj u v) :
    G.adjEdge h ∈ incident G u ∧ G.adjEdge h ∈ incident G v := by
  have heG := (G.adjEdge_spec h).1
  rcases (G.adjEdge_spec h).2 with hdir | hdir
  · exact ⟨mem_incident_iff.mpr ⟨heG, Or.inl hdir.1⟩,
      mem_incident_iff.mpr ⟨heG, Or.inr hdir.2⟩⟩
  · exact ⟨mem_incident_iff.mpr ⟨heG, Or.inr hdir.2⟩,
      mem_incident_iff.mpr ⟨heG, Or.inl hdir.1⟩⟩

/-- Adjacent vertices are distinct. -/
theorem FinGraph.Adj.ne {n : ℕ} {G : FinGraph n} {u v : Fin n}
    (h : G.Adj u v) : u ≠ v := by
  rcases h with ⟨e, _, hdir⟩
  rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact e.ne_endpoints
  · exact e.ne_endpoints.symm

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

/-! ## Petersen expansion (alpha = 1) -/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Finite kernel check over all subsets of `Fin 10`: empty and size above 5 are
exempt; every other set has cut size at least its cardinality. Uses `decide`
(not `native_decide`). -/
private theorem petersenGraph_expansion_decide :
    ∀ S : Finset (Fin 10),
      S.card = 0 ∨ 5 < S.card ∨
        S.card ≤ (edgeBoundary petersenGraph S).card := by
  decide

/-- Petersen has integer edge expansion factor 1 (pinned; tight on some 5-sets). -/
theorem petersenGraph_expansion : HasExpansion petersenGraph 1 := by
  intro S hne hcard
  rcases petersenGraph_expansion_decide S with h0 | hbig | hle
  · have : S = ∅ := card_eq_zero.mp h0
    exact (hne.ne_empty this).elim
  · have : S.card ≤ 5 := by omega
    exact (lt_irrefl _ (lt_of_le_of_lt this hbig)).elim
  · simpa [one_mul] using hle

/-! ## Heawood graph (generalized Petersen GP(7,2), n = 14) -/

/-- Helper: edge on `Fin 14` from concrete naturals. -/
private def hEdge (i j : ℕ) (hij : i < j := by decide) (hj : j < 14 := by decide) :
    FinEdge 14 :=
  finEdgeOf i j (lt_trans hij hj) hj hij

/-- The Heawood graph as GP(7,2): outer 7-cycle on `0..6`, spokes to `7..13`,
inner connections `i+7 -- (i+2 mod 7)+7`. Cubic cage on 14 vertices (21 edges). -/
def heawoodGraph : FinGraph 14 :=
  { hEdge 0 1, hEdge 1 2, hEdge 2 3, hEdge 3 4, hEdge 4 5, hEdge 5 6, hEdge 0 6,
    hEdge 0 7, hEdge 1 8, hEdge 2 9, hEdge 3 10, hEdge 4 11, hEdge 5 12, hEdge 6 13,
    hEdge 7 9, hEdge 8 10, hEdge 9 11, hEdge 10 12, hEdge 11 13, hEdge 7 12, hEdge 8 13 }

/-- Heawood has exactly 21 edges. -/
theorem heawoodGraph_card : heawoodGraph.card = 21 := by decide

/-- Heawood is 3-regular. -/
theorem heawoodGraph_regular : IsRegular heawoodGraph 3 := by
  intro v
  fin_cases v <;> decide

/-- Card-1 cuts are stars; regularity gives cut size 3 (seed for expansion). -/
theorem heawoodGraph_singleton_boundary (v : Fin 14) :
    (edgeBoundary heawoodGraph ({v} : Finset (Fin 14))).card = 3 := by
  simpa [edgeBoundary_singleton] using heawoodGraph_regular v

/-
Heawood `HasExpansion _ 1` is true combinatorially (verified externally on all
subsets of size 1..7) but the Lean kernel `decide` over `Fin 14` powersets did
not finish in-session. Expansion certification is deferred; construction and
3-regularity are certified above. Do not claim `heawoodGraph_expansion` until
a finishing kernel or combinatorial proof lands.
-/

end SATurday.ProofComplexity
