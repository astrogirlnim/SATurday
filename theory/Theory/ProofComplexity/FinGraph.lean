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

Cluster 1c certifies `heawoodGraph_expansion` at alpha = 1 via a bitmask
kernel check over all `2^14` masks (List.all + decide, not native_decide),
bridged to `HasExpansion` by relating masks to vertex sets and list cuts to
`edgeBoundary`. Half-size sets of card > 7 are exempt by the hypothesis.

Cluster 27 (2026-08-15): prism `Y_6` obstruction. Cubic regular on 12
vertices need not expand at factor 1; ladder like families are filtered out
of Block A.

LOG: R2 FinGraph API Petersen Heawood construction and expansion; prism obstruction
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

/-! ## Heawood expansion (alpha = 1), bitmask kernel check -/

set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

private instance : Std.Commutative (fun x y : ℕ => x ||| y) := ⟨Nat.or_comm⟩
private instance : Std.Associative (fun x y : ℕ => x ||| y) := ⟨Nat.or_assoc⟩

/-- Bitmask of a vertex set: bit `v.val` set iff `v ∈ S`. -/
private def heawoodFinsetToMask (S : Finset (Fin 14)) : ℕ :=
  S.fold (fun x y => x ||| y) 0 (fun v : Fin 14 => 2 ^ v.val)

private theorem heawood_testBit_finsetToMask (S : Finset (Fin 14)) (i : Fin 14) :
    (heawoodFinsetToMask S).testBit i.val = true ↔ i ∈ S := by
  induction S using Finset.induction_on with
  | empty => simp [heawoodFinsetToMask]
  | insert a s ha ih =>
    simp only [heawoodFinsetToMask, Finset.fold_insert ha]
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
    rw [mem_insert]
    constructor
    · rintro (hval | hbit)
      · exact Or.inl (Fin.ext hval).symm
      · exact Or.inr (ih.mp hbit)
    · rintro (hia | his)
      · exact Or.inl (congrArg Fin.val hia.symm)
      · exact Or.inr (ih.mpr his)

private theorem heawoodFinsetToMask_lt (S : Finset (Fin 14)) :
    heawoodFinsetToMask S < 2 ^ 14 := by
  induction S using Finset.induction_on with
  | empty => simp [heawoodFinsetToMask]
  | insert a s ha ih =>
    simp only [heawoodFinsetToMask, Finset.fold_insert ha]
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide : 1 < 2) a.isLt) ih

/-- Vertex set recovered from a bitmask. -/
private def heawoodSetOfMask (mask : ℕ) : Finset (Fin 14) :=
  univ.filter fun v => mask.testBit v.val

private theorem heawoodSetOfMask_finsetToMask (S : Finset (Fin 14)) :
    heawoodSetOfMask (heawoodFinsetToMask S) = S := by
  ext v; simp [heawoodSetOfMask, heawood_testBit_finsetToMask]

/-- Population count on the low 14 bits (List form keeps kernel checks light). -/
private def heawoodBitCount14 (mask : ℕ) : ℕ :=
  ((List.range 14).filter fun i => mask.testBit i).length

private theorem heawoodBitCount14_eq_setOfMask (mask : ℕ) :
    heawoodBitCount14 mask = (heawoodSetOfMask mask).card := by
  simp only [heawoodBitCount14, heawoodSetOfMask]
  have hmap : (List.finRange 14).map Fin.val = List.range 14 := by decide
  rw [← hmap, List.filter_map]
  change (List.map Fin.val
      (List.filter (fun v => mask.testBit v.val) (List.finRange 14))).length =
    (univ.filter fun v : Fin 14 => mask.testBit v.val).card
  rw [List.length_map]
  have hfilter :
      List.filter (fun v => mask.testBit v.val) (List.finRange 14) =
        List.filter (fun v => decide (mask.testBit v.val = true)) (List.finRange 14) := by
    congr 1
    ext v
    simp
  rw [hfilter]
  have hnodup :
      (List.filter (fun v => decide (mask.testBit v.val = true)) (List.finRange 14)).Nodup :=
    (List.nodup_finRange 14).filter _
  rw [← List.toFinset_card_of_nodup hnodup, List.toFinset_filter]
  congr 1
  ext v
  simp

private theorem heawoodBitCount14_finsetToMask (S : Finset (Fin 14)) :
    heawoodBitCount14 (heawoodFinsetToMask S) = S.card := by
  rw [heawoodBitCount14_eq_setOfMask, heawoodSetOfMask_finsetToMask]

/-- Nat endpoint pairs for the Heawood edge list (kernel-friendly cuts). -/
private def heawoodEdgePairs : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6),
    (0, 7), (1, 8), (2, 9), (3, 10), (4, 11), (5, 12), (6, 13),
    (7, 9), (8, 10), (9, 11), (10, 12), (11, 13), (7, 12), (8, 13)]

/-- Concrete `FinEdge` list matching `heawoodGraph`. -/
private def heawoodEdgePairList : List (FinEdge 14) :=
  [hEdge 0 1, hEdge 1 2, hEdge 2 3, hEdge 3 4, hEdge 4 5, hEdge 5 6, hEdge 0 6,
    hEdge 0 7, hEdge 1 8, hEdge 2 9, hEdge 3 10, hEdge 4 11, hEdge 5 12, hEdge 6 13,
    hEdge 7 9, hEdge 8 10, hEdge 9 11, hEdge 10 12, hEdge 11 13, hEdge 7 12, hEdge 8 13]

private theorem heawood_pairs_as_endpoints :
    heawoodEdgePairs =
      heawoodEdgePairList.map fun e => (e.val.1.val, e.val.2.val) := by decide

private theorem heawoodGraph_eq_pairList :
    heawoodGraph = heawoodEdgePairList.toFinset := by decide

private theorem heawoodEdgePairList_nodup : heawoodEdgePairList.Nodup := by decide

/-- Cut size of a bitmask against the Nat endpoint list. -/
private def heawoodCutMask (mask : ℕ) : ℕ :=
  (heawoodEdgePairs.filter fun e => mask.testBit e.1 != mask.testBit e.2).length

private theorem heawoodCutMask_eq_listFilter (mask : ℕ) :
    heawoodCutMask mask =
      (heawoodEdgePairList.filter fun e =>
        mask.testBit e.val.1.val != mask.testBit e.val.2.val).length := by
  simp only [heawoodCutMask]
  rw [heawood_pairs_as_endpoints, List.filter_map]
  simp only [List.length_map, Function.comp]
  rfl

private theorem heawood_mem_xor_iff (S : Finset (Fin 14)) (e : FinEdge 14) :
    ((e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.1 ∉ S ∧ e.val.2 ∈ S)) ↔
      ((heawoodFinsetToMask S).testBit e.val.1.val !=
        (heawoodFinsetToMask S).testBit e.val.2.val) := by
  have h1 := heawood_testBit_finsetToMask S e.val.1
  have h2 := heawood_testBit_finsetToMask S e.val.2
  cases hA : (heawoodFinsetToMask S).testBit e.val.1.val <;>
    cases hB : (heawoodFinsetToMask S).testBit e.val.2.val
  · have hn1 : e.val.1 ∉ S := by
      intro h; simp [h1.mpr h] at hA
    have hn2 : e.val.2 ∉ S := by
      intro h; simp [h2.mpr h] at hB
    simp [hn1, hn2]
  · have hn1 : e.val.1 ∉ S := by
      intro h; simp [h1.mpr h] at hA
    have hy2 : e.val.2 ∈ S := h2.mp (by simp [hB])
    simp [hn1, hy2]
  · have hy1 : e.val.1 ∈ S := h1.mp (by simp [hA])
    have hn2 : e.val.2 ∉ S := by
      intro h; simp [h2.mpr h] at hB
    simp [hy1, hn2]
  · have hy1 : e.val.1 ∈ S := h1.mp (by simp [hA])
    have hy2 : e.val.2 ∈ S := h2.mp (by simp [hB])
    simp [hy1, hy2]

private theorem heawood_edgeBoundary_card_eq_cutMask (S : Finset (Fin 14)) :
    (edgeBoundary heawoodGraph S).card = heawoodCutMask (heawoodFinsetToMask S) := by
  rw [heawoodCutMask_eq_listFilter]
  simp only [edgeBoundary]
  rw [heawoodGraph_eq_pairList]
  set Pbool := fun e : FinEdge 14 =>
    (heawoodFinsetToMask S).testBit e.val.1.val !=
      (heawoodFinsetToMask S).testBit e.val.2.val
  have hnodup : (heawoodEdgePairList.filter Pbool).Nodup :=
    heawoodEdgePairList_nodup.filter _
  rw [← List.toFinset_card_of_nodup hnodup, List.toFinset_filter]
  congr 1
  ext e
  simp only [mem_filter, List.mem_toFinset, Pbool]
  constructor
  · rintro ⟨he, hcut⟩
    exact ⟨he, (heawood_mem_xor_iff S e).mp hcut⟩
  · rintro ⟨he, hxor⟩
    exact ⟨he, (heawood_mem_xor_iff S e).mpr hxor⟩

/-- Mask-level expansion predicate (empty / over-half exempt). -/
private def heawoodMaskExpanding (mask : ℕ) : Bool :=
  let c := heawoodBitCount14 mask
  decide (c = 0 ∨ 14 < 2 * c ∨ c ≤ heawoodCutMask mask)

/-- Kernel check: every 14-bit mask is expanding at alpha = 1. -/
private theorem heawood_masks_expanding :
    (List.range 16384).all heawoodMaskExpanding = true := by
  decide

/-- Heawood has integer edge expansion factor 1. -/
theorem heawoodGraph_expansion : HasExpansion heawoodGraph 1 := by
  intro S hne hhalf
  have hm : heawoodFinsetToMask S ∈ List.range 16384 :=
    List.mem_range.mpr (heawoodFinsetToMask_lt S)
  have hbool : heawoodMaskExpanding (heawoodFinsetToMask S) = true :=
    (List.all_eq_true.mp heawood_masks_expanding) _ hm
  have hc : heawoodBitCount14 (heawoodFinsetToMask S) = S.card :=
    heawoodBitCount14_finsetToMask S
  have hcut :
      (edgeBoundary heawoodGraph S).card = heawoodCutMask (heawoodFinsetToMask S) :=
    heawood_edgeBoundary_card_eq_cutMask S
  simp only [heawoodMaskExpanding, hc] at hbool
  have hprop :
      S.card = 0 ∨ 14 < 2 * S.card ∨
        S.card ≤ heawoodCutMask (heawoodFinsetToMask S) :=
    of_decide_eq_true hbool
  rcases hprop with h0 | hbig | hle
  · exact (hne.ne_empty (card_eq_zero.mp h0)).elim
  · exact (lt_irrefl _ (lt_of_lt_of_le hbig hhalf)).elim
  · simpa [one_mul, hcut] using hle

/-! ## Cluster 27: prism ladder obstruction (Block A family filter)

The circular ladder / prism `Y_m = C_m □ K₂` is the obvious unbounded cubic
family. A band of three columns has cut size 4 and order 6, so integer
expansion factor 1 already fails at `m = 6` (`n = 12`). Ladder like cubics
are not Block A expander candidates. -/

/-- Helper: edge on `Fin 12` for the `m = 6` prism. -/
private def pr6Edge (i j : ℕ) (hij : i < j := by decide) (hj : j < 12 := by decide) :
    FinEdge 12 :=
  finEdgeOf i j (lt_trans hij hj) hj hij

/-- Prism `Y_6` on 12 vertices: outer 6-cycle, inner 6-cycle, six spokes.
Canonical obstruction witness for ladder like cubics. -/
def prismGraph6 : FinGraph 12 :=
  { pr6Edge 0 1, pr6Edge 1 2, pr6Edge 2 3, pr6Edge 3 4, pr6Edge 4 5, pr6Edge 0 5,
    pr6Edge 6 7, pr6Edge 7 8, pr6Edge 8 9, pr6Edge 9 10, pr6Edge 10 11, pr6Edge 6 11,
    pr6Edge 0 6, pr6Edge 1 7, pr6Edge 2 8, pr6Edge 3 9, pr6Edge 4 10, pr6Edge 5 11 }

/-- Prism `Y_6` has 18 edges. -/
theorem prismGraph6_card : prismGraph6.card = 18 := by decide

/-- Prism `Y_6` is 3-regular. -/
theorem prismGraph6_regular : IsRegular prismGraph6 3 := by
  intro v
  fin_cases v <;> decide

/-- Three-column band `{0,1,2,6,7,8}`: the standard prism cut of size 4. -/
def prismGraph6Band : Finset (Fin 12) :=
  {0, 1, 2, 6, 7, 8}

theorem prismGraph6Band_card : prismGraph6Band.card = 6 := by decide

theorem prismGraph6Band_boundary_card :
    (edgeBoundary prismGraph6 prismGraph6Band).card = 4 := by decide

/-- Half-size hypothesis for the band: `2 * 6 ≤ 12`. -/
theorem prismGraph6Band_half : 2 * prismGraph6Band.card ≤ 12 := by
  simp [prismGraph6Band_card]

/-- The band is a nonempty medium set with cut strictly below its card. -/
theorem prismGraph6Band_not_expanding :
    prismGraph6Band.Nonempty ∧
      2 * prismGraph6Band.card ≤ 12 ∧
        (edgeBoundary prismGraph6 prismGraph6Band).card < prismGraph6Band.card := by
  refine ⟨⟨0, by decide⟩, prismGraph6Band_half, ?_⟩
  simp [prismGraph6Band_boundary_card, prismGraph6Band_card]

/-- Prism `Y_6` fails integer expansion factor 1. -/
theorem not_hasExpansion_prismGraph6 : ¬ HasExpansion prismGraph6 1 := by
  intro h
  have hband := h prismGraph6Band ⟨0, by decide⟩ prismGraph6Band_half
  have hlt :
      (edgeBoundary prismGraph6 prismGraph6Band).card < prismGraph6Band.card :=
    prismGraph6Band_not_expanding.2.2
  exact (not_le_of_gt hlt) (by simpa [one_mul] using hband)

/-- Packaging: a cubic regular graph on 12 vertices need not expand at factor 1;
the prism is a concrete counterexample (family filter for Block A). -/
theorem exists_cubic_regular_not_expanding_twelve :
    ∃ G : FinGraph 12, IsRegular G 3 ∧ ¬ HasExpansion G 1 :=
  ⟨prismGraph6, prismGraph6_regular, not_hasExpansion_prismGraph6⟩

end SATurday.ProofComplexity
