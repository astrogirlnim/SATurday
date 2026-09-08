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

end SATurday.ProofComplexity
