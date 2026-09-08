import Theory.ProofComplexity.FinGraph
import Mathlib.Tactic

/-!
# Margulis Gabber Galil scaffolding (R2 Cluster 29)

Block A inhabit route (prove 2026-09-08): cubic Inv family via 8 regular MGG
on `(Z/mZ)²` then cubicization. This module lands vertex encoding and the
simple graph edge set. Spectral Inv and replacement product stay later.

Classical generators (Trevisan / Hoory): from `(x,y)` the eight neighbors
`(x±1,y)`, `(x,y±1)`, `S=(x,x+y)`, `S⁻¹=(x,y-x)`, `T=(x+y,y)`, `T⁻¹=(x-y,y)`,
all mod `m`.

LOG: R2 Cluster 29 MGG encode decode neighbor graph scaffolding
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-- Decode `Fin (m * m)` as row major `(row, col)`. -/
def mggDecode {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) : Fin m × Fin m :=
  (⟨v.val / m, (Nat.div_lt_iff_lt_mul hm).2 v.isLt⟩,
    ⟨v.val % m, Nat.mod_lt v.val hm⟩)

/-- Encode `(row, col)` to `Fin (m * m)`. -/
def mggEncode {m : ℕ} (_hm : 0 < m) (p : Fin m × Fin m) : Fin (m * m) :=
  ⟨p.1.val * m + p.2.val, by
    have h1 : p.1.val + 1 ≤ m := Nat.succ_le_of_lt p.1.isLt
    have h2 : p.2.val < m := p.2.isLt
    calc
      p.1.val * m + p.2.val
          < p.1.val * m + m := Nat.add_lt_add_left h2 _
      _ = (p.1.val + 1) * m := by rw [Nat.succ_mul]
      _ ≤ m * m := Nat.mul_le_mul_right m h1⟩

theorem mggEncode_decode {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggEncode hm (mggDecode hm v) = v := by
  apply Fin.ext
  simp only [mggEncode, mggDecode]
  -- `div_add_mod` is `m * (v/m) + v%m`; commute the product.
  simpa [Nat.mul_comm] using Nat.div_add_mod v.val m

theorem mggDecode_encode {m : ℕ} (hm : 0 < m) (p : Fin m × Fin m) :
    mggDecode hm (mggEncode hm p) = p := by
  apply Prod.ext
  · apply Fin.ext
    simp only [mggEncode, mggDecode]
    have h := Nat.add_mul_div_left p.2.val p.1.val hm
    rw [Nat.mul_comm p.1.val m, Nat.add_comm, h, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]
  · apply Fin.ext
    simp only [mggEncode, mggDecode]
    exact Nat.mul_add_mod_of_lt p.2.isLt

/-- Local `NeZero` from positivity, for `OfNat` on `Fin m`. -/
private theorem mggNeZero {m : ℕ} (hm : 0 < m) : NeZero m := ⟨ne_of_gt hm⟩

/-- Eight MGG neighbor indices. -/
def mggNeighbor {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) : Fin (m * m) :=
  letI : NeZero m := mggNeZero hm
  let x := (mggDecode hm v).1
  let y := (mggDecode hm v).2
  if s.val = 0 then mggEncode hm (x + 1, y)
  else if s.val = 1 then mggEncode hm (x - 1, y)
  else if s.val = 2 then mggEncode hm (x, y + 1)
  else if s.val = 3 then mggEncode hm (x, y - 1)
  else if s.val = 4 then mggEncode hm (x, x + y)
  else if s.val = 5 then mggEncode hm (x, y - x)
  else if s.val = 6 then mggEncode hm (x + y, y)
  else mggEncode hm (x - y, y)

/-- Undirected simple edge between `v` and `mggNeighbor v s` when distinct. -/
def mggEdgeOf {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    Option (FinEdge (m * m)) :=
  let w := mggNeighbor hm v s
  if h : v.val < w.val then
    some ⟨(v, w), h⟩
  else if h : w.val < v.val then
    some ⟨(w, v), h⟩
  else
    none

/-- Margulis Gabber Galil simple graph on `m * m` vertices. -/
def mggGraph (m : ℕ) (hm : 0 < m) : FinGraph (m * m) :=
  (Finset.univ : Finset (Fin (m * m))).biUnion fun v =>
    (Finset.univ : Finset (Fin 8)).biUnion fun s =>
      match mggEdgeOf hm v s with
      | some e => {e}
      | none => ∅

theorem mem_mggGraph_of_edgeOf {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8)
    {e : FinEdge (m * m)} (he : mggEdgeOf hm v s = some e) :
    e ∈ mggGraph m hm := by
  refine mem_biUnion.mpr ⟨v, mem_univ v, ?_⟩
  refine mem_biUnion.mpr ⟨s, mem_univ s, ?_⟩
  simp [he]

theorem mgg_three_vertex_card : Fintype.card (Fin (3 * 3)) = 9 := by decide

/-! ## Cluster 29b: simple MGG is not 8-regular

Classical MGG is an 8-regular multigraph. Our `FinGraph` drops self-loops, so
`S`/`T` generators vanish on the axes. Exact `IsRegular (mggGraph m _) 8` fails
already at `m = 3` (origin degree 4). Intermediate inhabit must track
multiplicity or restate the degree hypothesis. -/

private theorem hm3 : (0 : ℕ) < 3 := by decide

/-- Origin vertex on the `m = 3` torus. -/
def mggOrigin3 : Fin (3 * 3) :=
  mggEncode hm3 (⟨0, by decide⟩, ⟨0, by decide⟩)

/-- Concrete: origin degree on `m = 3` is 4 (four translations; S/T are loops). -/
theorem mggOrigin3_degree : degree (mggGraph 3 hm3) mggOrigin3 = 4 := by
  decide

/-- Hence the simple `m = 3` MGG is not 8-regular. -/
theorem not_isRegular_mggGraph_three_eight :
    ¬ IsRegular (mggGraph 3 hm3) 8 := by
  intro h
  have := h mggOrigin3
  simp [mggOrigin3_degree] at this


/-! ## Cluster 29c: Inv-only intermediate pin + translation adjacency

Prove accept_prose 2026-09-08: intermediate pin is connectivity plus
`HasExpansionInv (mggGraph m _) mggInvK` (no simple regularity 8).
This cluster certifies constants and right/up adjacency; full connectivity
and Inv family stay in `MGGFrontier`. -/

def mggInvK : ℕ := 4
def mggInformativeFloor : ℕ := 6
def mggRight : Fin 8 := ⟨0, by decide⟩
def mggUp : Fin 8 := ⟨2, by decide⟩

/-- On `Fin k` with `1 < k`, successor is irreflexive. (Fails for `k = 1`.) -/
theorem Fin.add_one_ne_of_one_lt {k : ℕ} [NeZero k] (hk : 1 < k) (x : Fin k) :
    x + 1 ≠ x := by
  intro h
  have hval' := congrArg Fin.val h
  rw [Fin.val_add] at hval'
  have hone : ((1 : Fin k) : ℕ) = 1 := by
    change (1 : ℕ) % k = 1
    exact Nat.mod_eq_of_lt hk
  have hval : (x.val + 1) % k = x.val := by
    rwa [hone] at hval'
  have hx : x.val < k := x.isLt
  by_cases hlt : x.val + 1 < k
  · have heq : (x.val + 1) % k = x.val + 1 := Nat.mod_eq_of_lt hlt
    rw [heq] at hval
    exact (Nat.ne_of_gt (Nat.lt_succ_self x.val)) hval
  · have hkm : x.val + 1 = k := by omega
    rw [hkm, Nat.mod_self] at hval
    omega

theorem mggNeighbor_right_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggRight =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1 + 1, (mggDecode hm v).2) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_right_ne {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggRight ≠ v := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hx := (Prod.ext_iff.mp (by
    simpa [mggNeighbor_right_eq hm0, mggDecode_encode] using
      congrArg (mggDecode hm0) h)).1
  exact Fin.add_one_ne_of_one_lt hm (mggDecode hm0 v).1 hx

theorem mggNeighbor_up_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggUp =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2 + 1) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_up_ne {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggUp ≠ v := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hy := (Prod.ext_iff.mp (by
    simpa [mggNeighbor_up_eq hm0, mggDecode_encode] using
      congrArg (mggDecode hm0) h)).2
  exact Fin.add_one_ne_of_one_lt hm (mggDecode hm0 v).2 hy

theorem mggEdgeOf_eq_some_of_ne {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8)
    (hne : mggNeighbor hm v s ≠ v) :
    ∃ e, mggEdgeOf hm v s = some e ∧
      ((e.val.1 = v ∧ e.val.2 = mggNeighbor hm v s) ∨
        (e.val.1 = mggNeighbor hm v s ∧ e.val.2 = v)) := by
  dsimp [mggEdgeOf]
  set w := mggNeighbor hm v s
  by_cases hlt : v.val < w.val
  · refine ⟨⟨(v, w), hlt⟩, ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp [hlt]
  · have hwv : w.val < v.val := by
      have : w.val ≠ v.val := fun heq => hne (Fin.ext heq)
      omega
    refine ⟨⟨(w, v), hwv⟩, ?_, Or.inr ⟨rfl, rfl⟩⟩
    simp [hlt, hwv]

theorem mgg_adj_right {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Adj v
      (mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggRight) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  obtain ⟨e, he, hends⟩ :=
    mggEdgeOf_eq_some_of_ne hm0 v mggRight (mggNeighbor_right_ne hm v)
  refine ⟨e, mem_mggGraph_of_edgeOf hm0 v mggRight he, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem mgg_adj_up {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Adj v
      (mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggUp) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  obtain ⟨e, he, hends⟩ :=
    mggEdgeOf_eq_some_of_ne hm0 v mggUp (mggNeighbor_up_ne hm v)
  refine ⟨e, mem_mggGraph_of_edgeOf hm0 v mggUp he, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- One right step from an encoded cell. -/
theorem mgg_adj_right_encode {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Adj
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x + ⟨1, hm⟩, y)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  have hadj := mgg_adj_right hm (mggEncode hm0 (x, y))
  have hneq :
      mggNeighbor hm0 (mggEncode hm0 (x, y)) mggRight =
        mggEncode hm0 (x + ⟨1, hm⟩, y) := by
    rw [mggNeighbor_right_eq hm0, mggDecode_encode]
    congr 1
    apply Prod.ext
    · exact Fin.ext (by
        simp only [Fin.val_add, Fin.val_mk]
        have : ((1 : Fin m) : ℕ) = 1 := by
          change 1 % m = 1
          exact Nat.mod_eq_of_lt hm
        simp [this])
    · rfl
  simpa [hneq] using hadj

/-- One up step from an encoded cell. -/
theorem mgg_adj_up_encode {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Adj
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y + ⟨1, hm⟩)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  have hadj := mgg_adj_up hm (mggEncode hm0 (x, y))
  have hneq :
      mggNeighbor hm0 (mggEncode hm0 (x, y)) mggUp =
        mggEncode hm0 (x, y + ⟨1, hm⟩) := by
    rw [mggNeighbor_up_eq hm0, mggDecode_encode]
    congr 1
    apply Prod.ext
    · rfl
    · exact Fin.ext (by
        simp only [Fin.val_add, Fin.val_mk]
        have : ((1 : Fin m) : ℕ) = 1 := by
          change 1 % m = 1
          exact Nat.mod_eq_of_lt hm
        simp [this])
  simpa [hneq] using hadj

namespace MGGFrontier

/-- Torus connectivity via translation walks; next formalize discharges using
`mgg_adj_right_encode` / `mgg_adj_up_encode`. -/
theorem mggGraph_isConnected {m : ℕ} (hm : 0 < m) :
    (mggGraph m hm).IsConnected := by
  sorry

/-- Intermediate Block A pin: unbounded simple MGG Inv expanders (no regularity). -/
theorem exists_mgg_simple_hasExpansionInv_family :
    ∀ N : ℕ, ∃ (m : ℕ) (hm : 0 < m),
      max N mggInformativeFloor ≤ m ∧
        (mggGraph m hm).IsConnected ∧
          HasExpansionInv (mggGraph m hm) mggInvK := by
  sorry

end MGGFrontier

end SATurday.ProofComplexity
