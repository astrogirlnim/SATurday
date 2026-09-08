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

/-! ## Cluster 29d: torus connectivity via translation walks -/

/-- Pack `n % m` as an element of `Fin m`. -/
private def mggFinMod {m : ℕ} (hm : 0 < m) (n : ℕ) : Fin m :=
  ⟨n % m, Nat.mod_lt n hm⟩

/-- `n` successive right steps (needs `1 < m`). -/
theorem mgg_reachable_right_pow {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    ∀ n : ℕ,
      (mggGraph m (lt_trans Nat.zero_lt_one hm)).Reachable
        (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
        (mggEncode (lt_trans Nat.zero_lt_one hm)
          (x + mggFinMod (lt_trans Nat.zero_lt_one hm) n, y)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro n
  induction n with
  | zero =>
    have hx : x + mggFinMod hm0 0 = x := by
      apply Fin.ext
      simp [mggFinMod, Nat.zero_mod]
    simpa [hx] using
      (Relation.ReflTransGen.refl :
        (mggGraph m hm0).Reachable
          (mggEncode hm0 (x, y)) (mggEncode hm0 (x, y)))
  | succ n ih =>
    have hstep :
        (mggGraph m hm0).Adj
          (mggEncode hm0 (x + mggFinMod hm0 n, y))
          (mggEncode hm0 ((x + mggFinMod hm0 n) + ⟨1, hm⟩, y)) :=
      mgg_adj_right_encode hm (x + mggFinMod hm0 n) y
    have heq :
        (x + mggFinMod hm0 n) + ⟨1, hm⟩ = x + mggFinMod hm0 (n + 1) := by
      apply Fin.ext
      simp only [mggFinMod, Fin.val_add, Fin.val_mk]
      -- ((x.val + n%m) % m + 1) % m = (x.val + (n+1)%m) % m
      have hr : (n + 1) % m = (n % m + 1) % m := by
        calc (n + 1) % m
            = (n % m + 1 % m) % m := by rw [Nat.add_mod]
          _ = (n % m + 1) % m := by rw [Nat.mod_eq_of_lt hm]
      rw [hr]
      calc (((x.val + n % m) % m) + 1) % m
          = ((x.val + n % m) + 1) % m := by rw [Nat.mod_add_mod]
        _ = (x.val + (n % m + 1)) % m := by rw [Nat.add_assoc]
        _ = (x.val + (n % m + 1) % m) % m := by rw [Nat.add_mod_mod]
    refine Relation.ReflTransGen.tail ih ?_
    simpa [heq] using hstep

/-- `n` successive up steps (needs `1 < m`). -/
theorem mgg_reachable_up_pow {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    ∀ n : ℕ,
      (mggGraph m (lt_trans Nat.zero_lt_one hm)).Reachable
        (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
        (mggEncode (lt_trans Nat.zero_lt_one hm)
          (x, y + mggFinMod (lt_trans Nat.zero_lt_one hm) n)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro n
  induction n with
  | zero =>
    have hy : y + mggFinMod hm0 0 = y := by
      apply Fin.ext
      simp [mggFinMod, Nat.zero_mod]
    simpa [hy] using
      (Relation.ReflTransGen.refl :
        (mggGraph m hm0).Reachable
          (mggEncode hm0 (x, y)) (mggEncode hm0 (x, y)))
  | succ n ih =>
    have hstep :
        (mggGraph m hm0).Adj
          (mggEncode hm0 (x, y + mggFinMod hm0 n))
          (mggEncode hm0 (x, (y + mggFinMod hm0 n) + ⟨1, hm⟩)) :=
      mgg_adj_up_encode hm x (y + mggFinMod hm0 n)
    have heq :
        (y + mggFinMod hm0 n) + ⟨1, hm⟩ = y + mggFinMod hm0 (n + 1) := by
      apply Fin.ext
      simp only [mggFinMod, Fin.val_add, Fin.val_mk]
      have hr : (n + 1) % m = (n % m + 1) % m := by
        calc (n + 1) % m
            = (n % m + 1 % m) % m := by rw [Nat.add_mod]
          _ = (n % m + 1) % m := by rw [Nat.mod_eq_of_lt hm]
      rw [hr]
      calc (((y.val + n % m) % m) + 1) % m
          = ((y.val + n % m) + 1) % m := by rw [Nat.mod_add_mod]
        _ = (y.val + (n % m + 1)) % m := by rw [Nat.add_assoc]
        _ = (y.val + (n % m + 1) % m) % m := by rw [Nat.add_mod_mod]
    refine Relation.ReflTransGen.tail ih ?_
    simpa [heq] using hstep

/-- Same column: right walk from `x₁` to `x₂`. -/
theorem mgg_reachable_right_to {m : ℕ} (hm : 1 < m) (x₁ x₂ y : Fin m) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x₁, y))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x₂, y)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  have h := mgg_reachable_right_pow hm x₁ y (x₂ - x₁).val
  have hx : x₁ + mggFinMod hm0 (x₂ - x₁).val = x₂ :=
    Fin.ext <| by
      have hlt : (x₂ - x₁).val < m := (x₂ - x₁).isLt
      simpa [mggFinMod, Nat.mod_eq_of_lt hlt] using
        congrArg Fin.val (add_sub_cancel x₁ x₂)
  simpa [hx] using h

/-- Same row: up walk from `y₁` to `y₂`. -/
theorem mgg_reachable_up_to {m : ℕ} (hm : 1 < m) (x y₁ y₂ : Fin m) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y₁))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y₂)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  have h := mgg_reachable_up_pow hm x y₁ (y₂ - y₁).val
  have hy : y₁ + mggFinMod hm0 (y₂ - y₁).val = y₂ :=
    Fin.ext <| by
      have hlt : (y₂ - y₁).val < m := (y₂ - y₁).isLt
      simpa [mggFinMod, Nat.mod_eq_of_lt hlt] using
        congrArg Fin.val (add_sub_cancel y₁ y₂)
  simpa [hy] using h

/-- Any two encoded cells are reachable when `1 < m`. -/
theorem mgg_reachable_encode {m : ℕ} (hm : 1 < m) (p q : Fin m × Fin m) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) p)
      (mggEncode (lt_trans Nat.zero_lt_one hm) q) :=
  Relation.ReflTransGen.trans
    (mgg_reachable_right_to hm p.1 q.1 p.2)
    (mgg_reachable_up_to hm q.1 p.2 q.2)

/-- Torus connectivity: translation generators alone connect `(Z/mZ)²`. -/
theorem mggGraph_isConnected {m : ℕ} (hm : 0 < m) :
    (mggGraph m hm).IsConnected := by
  intro u v
  by_cases hm1 : 1 < m
  · rw [show u = mggEncode hm (mggDecode hm u) from (mggEncode_decode hm u).symm]
    rw [show v = mggEncode hm (mggDecode hm v) from (mggEncode_decode hm v).symm]
    convert mgg_reachable_encode hm1 (mggDecode hm u) (mggDecode hm v)
  · have hm_eq : m = 1 := by omega
    subst hm_eq
    have huv : u = v := Fin.ext <|
      (Nat.lt_one_iff.mp u.isLt).trans (Nat.lt_one_iff.mp v.isLt).symm
    subst huv
    exact Relation.ReflTransGen.refl

/-! ## Cluster 29e: left/down adjacency, min degree, Inv family packaging

Connectivity is certified. Remaining Gabber Galil gap is Inv. This cluster
lands the other two translation generators plus pairwise translation
distinctness for `m ≥ 3`, and packages the unbounded family from a uniform Inv
hypothesis so Frontier holds only the spectral gap. -/

def mggLeft : Fin 8 := ⟨1, by decide⟩
def mggDown : Fin 8 := ⟨3, by decide⟩

/-- On `Fin k` with `1 < k`, predecessor is irreflexive. -/
theorem Fin.sub_one_ne_of_one_lt {k : ℕ} [NeZero k] (hk : 1 < k) (x : Fin k) :
    x - 1 ≠ x := by
  intro h
  have : x = x + 1 := by
    calc
      x = (x - 1) + 1 := (sub_add_cancel x 1).symm
      _ = x + 1 := by rw [h]
  exact Fin.add_one_ne_of_one_lt hk x this.symm

/-- For `3 ≤ k`, successor and predecessor differ (`2 ≠ 0` in `Fin k`). -/
theorem Fin.add_one_ne_sub_one_of_three_le {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : Fin k) : x + 1 ≠ x - 1 := by
  intro h
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk
  have h2lt : 2 < k := lt_of_lt_of_le (by decide : 2 < 3) hk
  -- From x+1 = x-1, adding 1 yields x+2 = x, so 2 = 0 in Fin k.
  have h2 : x + (2 : Fin k) = x := by
    have h21 : (2 : Fin k) = (1 : Fin k) + 1 := by
      apply Fin.ext
      change (2 % k) = ((1 % k) + (1 % k)) % k
      simp [Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt h2lt]
    calc
      x + 2 = x + (1 + 1) := by rw [h21]
      _ = x + 1 + 1 := by rw [add_assoc]
      _ = (x - 1) + 1 := by rw [h]
      _ = x := sub_add_cancel x 1
  have htwo : (2 : Fin k) = 0 := add_left_cancel (a := x) (by simpa using h2)
  have h2ne : (2 : Fin k) ≠ 0 :=
    Fin.ne_of_gt (by
      change (0 : ℕ) < 2 % k
      simpa [Nat.mod_eq_of_lt h2lt] using (by decide : (0 : ℕ) < 2))
  exact h2ne htwo

theorem mggNeighbor_left_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggLeft =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1 - 1, (mggDecode hm v).2) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_left_ne {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggLeft ≠ v := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hx := (Prod.ext_iff.mp (by
    simpa [mggNeighbor_left_eq hm0, mggDecode_encode] using
      congrArg (mggDecode hm0) h)).1
  exact Fin.sub_one_ne_of_one_lt hm (mggDecode hm0 v).1 hx

theorem mggNeighbor_down_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggDown =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2 - 1) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_down_ne {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggDown ≠ v := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hy := (Prod.ext_iff.mp (by
    simpa [mggNeighbor_down_eq hm0, mggDecode_encode] using
      congrArg (mggDecode hm0) h)).2
  exact Fin.sub_one_ne_of_one_lt hm (mggDecode hm0 v).2 hy

theorem mgg_adj_left {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Adj v
      (mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggLeft) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  obtain ⟨e, he, hends⟩ :=
    mggEdgeOf_eq_some_of_ne hm0 v mggLeft (mggNeighbor_left_ne hm v)
  refine ⟨e, mem_mggGraph_of_edgeOf hm0 v mggLeft he, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem mgg_adj_down {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    (mggGraph m (lt_trans Nat.zero_lt_one hm)).Adj v
      (mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggDown) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  obtain ⟨e, he, hends⟩ :=
    mggEdgeOf_eq_some_of_ne hm0 v mggDown (mggNeighbor_down_ne hm v)
  refine ⟨e, mem_mggGraph_of_edgeOf hm0 v mggDown he, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Decode both sides of a neighbor equality after unfolding generator equations. -/
private theorem mgg_decode_neighbor_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m))
    {s t : Fin 8} {p q : Fin m × Fin m}
    (hs : mggNeighbor hm v s = mggEncode hm p)
    (ht : mggNeighbor hm v t = mggEncode hm q)
    (heq : mggNeighbor hm v s = mggNeighbor hm v t) :
    p = q := by
  have hdec := congrArg (mggDecode hm) heq
  rw [hs, ht, mggDecode_encode, mggDecode_encode] at hdec
  exact hdec

/-- Horizontal translations disagree when `3 ≤ m`. -/
theorem mggNeighbor_right_ne_left {m : ℕ} (hm : 3 ≤ m) (v : Fin (m * m)) :
    mggNeighbor (lt_of_lt_of_le (by decide : 0 < 3) hm) v mggRight ≠
      mggNeighbor (lt_of_lt_of_le (by decide : 0 < 3) hm) v mggLeft := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hpq := mgg_decode_neighbor_eq hm0 v
    (mggNeighbor_right_eq hm0 v) (mggNeighbor_left_eq hm0 v) h
  exact Fin.add_one_ne_sub_one_of_three_le hm (mggDecode hm0 v).1
    (Prod.ext_iff.mp hpq).1

/-- Vertical translations disagree when `3 ≤ m`. -/
theorem mggNeighbor_up_ne_down {m : ℕ} (hm : 3 ≤ m) (v : Fin (m * m)) :
    mggNeighbor (lt_of_lt_of_le (by decide : 0 < 3) hm) v mggUp ≠
      mggNeighbor (lt_of_lt_of_le (by decide : 0 < 3) hm) v mggDown := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hpq := mgg_decode_neighbor_eq hm0 v
    (mggNeighbor_up_eq hm0 v) (mggNeighbor_down_eq hm0 v) h
  exact Fin.add_one_ne_sub_one_of_three_le hm (mggDecode hm0 v).2
    (Prod.ext_iff.mp hpq).2

/-- Right versus up: first coordinates force `1 = 0` when `1 < m`. -/
theorem mggNeighbor_right_ne_up {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggRight ≠
      mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggUp := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hpq := mgg_decode_neighbor_eq hm0 v
    (mggNeighbor_right_eq hm0 v) (mggNeighbor_up_eq hm0 v) h
  exact Fin.add_one_ne_of_one_lt hm (mggDecode hm0 v).1
    (Prod.ext_iff.mp hpq).1

/-- Right versus down. -/
theorem mggNeighbor_right_ne_down {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggRight ≠
      mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggDown := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hpq := mgg_decode_neighbor_eq hm0 v
    (mggNeighbor_right_eq hm0 v) (mggNeighbor_down_eq hm0 v) h
  exact Fin.add_one_ne_of_one_lt hm (mggDecode hm0 v).1
    (Prod.ext_iff.mp hpq).1

/-- Left versus up. -/
theorem mggNeighbor_left_ne_up {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggLeft ≠
      mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggUp := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hpq := mgg_decode_neighbor_eq hm0 v
    (mggNeighbor_left_eq hm0 v) (mggNeighbor_up_eq hm0 v) h
  exact Fin.sub_one_ne_of_one_lt hm (mggDecode hm0 v).1
    (Prod.ext_iff.mp hpq).1

/-- Left versus down. -/
theorem mggNeighbor_left_ne_down {m : ℕ} (hm : 1 < m) (v : Fin (m * m)) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggLeft ≠
      mggNeighbor (lt_trans Nat.zero_lt_one hm) v mggDown := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggNeZero hm0
  intro h
  have hpq := mgg_decode_neighbor_eq hm0 v
    (mggNeighbor_left_eq hm0 v) (mggNeighbor_down_eq hm0 v) h
  exact Fin.sub_one_ne_of_one_lt hm (mggDecode hm0 v).1
    (Prod.ext_iff.mp hpq).1

/-- Family packaging: uniform Inv on large `m` yields the intermediate pin. -/
theorem exists_mgg_simple_hasExpansionInv_family_of_inv
    (hInv : ∀ (m : ℕ) (hm0 : 0 < m),
      mggInformativeFloor ≤ m → HasExpansionInv (mggGraph m hm0) mggInvK) :
    ∀ N : ℕ, ∃ (m : ℕ) (hm : 0 < m),
      max N mggInformativeFloor ≤ m ∧
        (mggGraph m hm).IsConnected ∧
          HasExpansionInv (mggGraph m hm) mggInvK := by
  intro N
  let m := max N mggInformativeFloor
  have hm0 : 0 < m :=
    lt_of_lt_of_le (by decide : 0 < mggInformativeFloor)
      (le_max_right N mggInformativeFloor)
  refine ⟨m, hm0, le_rfl, mggGraph_isConnected (m := m) hm0, ?_⟩
  exact hInv m hm0 (le_max_right N mggInformativeFloor)

/-! ## Cluster 30: axis set, loops, multi-cut surface, Nat Cheeger slack

Prove accept_prose 2026-09-08 (Gabber Galil to Cheeger to axis loss to Inv 4).
This cluster lands combinatorial surface lemmas (i)(ii)(iv) and a labeled
multi-cut counter toward (vii). Spectral gap and full loss algebra stay Frontier. -/

/-- Shear generator `S`: `(x,y) ↦ (x, x+y)`. -/
def mggS : Fin 8 := ⟨4, by decide⟩
/-- Inverse shear `S⁻¹`: `(x,y) ↦ (x, y-x)`. -/
def mggSinv : Fin 8 := ⟨5, by decide⟩
/-- Shear generator `T`: `(x,y) ↦ (x+y, y)`. -/
def mggT : Fin 8 := ⟨6, by decide⟩
/-- Inverse shear `T⁻¹`: `(x,y) ↦ (x-y, y)`. -/
def mggTinv : Fin 8 := ⟨7, by decide⟩

/-- Shear generator indices (the only generators that can loop for `1 < m`). -/
def mggShearGens : Finset (Fin 8) := {mggS, mggSinv, mggT, mggTinv}

theorem mggShearGens_card : mggShearGens.card = 4 := by decide

/-- Axis vertices: first or second torus coordinate is zero. -/
def mggAxis (m : ℕ) (hm : 0 < m) : Finset (Fin (m * m)) :=
  letI : NeZero m := mggNeZero hm
  (Finset.univ : Finset (Fin (m * m))).filter fun v =>
    (mggDecode hm v).1 = 0 ∨ (mggDecode hm v).2 = 0

theorem mem_mggAxis_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    v ∈ mggAxis m hm ↔
      letI : NeZero m := mggNeZero hm
      (mggDecode hm v).1 = 0 ∨ (mggDecode hm v).2 = 0 := by
  letI : NeZero m := mggNeZero hm
  simp [mggAxis]

/-- Row zero encodings. -/
def mggRow0 (m : ℕ) (hm : 0 < m) : Finset (Fin (m * m)) :=
  (Finset.univ : Finset (Fin m)).image fun y => mggEncode hm (⟨0, hm⟩, y)

/-- Column zero encodings. -/
def mggCol0 (m : ℕ) (hm : 0 < m) : Finset (Fin (m * m)) :=
  (Finset.univ : Finset (Fin m)).image fun x => mggEncode hm (x, ⟨0, hm⟩)

theorem mggRow0_card {m : ℕ} (hm : 0 < m) : (mggRow0 m hm).card = m := by
  rw [mggRow0, card_image_of_injective]
  · simp [Finset.card_univ]
  · intro y₁ y₂ h
    exact (Prod.ext_iff.mp ((mggDecode_encode hm _).symm.trans
      ((congrArg (mggDecode hm) h).trans (mggDecode_encode hm _)))).2

theorem mggCol0_card {m : ℕ} (hm : 0 < m) : (mggCol0 m hm).card = m := by
  rw [mggCol0, card_image_of_injective]
  · simp [Finset.card_univ]
  · intro x₁ x₂ h
    exact (Prod.ext_iff.mp ((mggDecode_encode hm _).symm.trans
      ((congrArg (mggDecode hm) h).trans (mggDecode_encode hm _)))).1

theorem mggAxis_eq_row0_union_col0 {m : ℕ} (hm : 0 < m) :
    mggAxis m hm = mggRow0 m hm ∪ mggCol0 m hm := by
  letI : NeZero m := mggNeZero hm
  ext v
  constructor
  · intro hv
    have h := (mem_mggAxis_iff hm v).mp hv
    rw [mem_union]
    rcases h with hx | hy
    · refine Or.inl ?_
      refine mem_image.mpr ⟨(mggDecode hm v).2, mem_univ _, ?_⟩
      have hx0 : (mggDecode hm v).1 = ⟨0, hm⟩ := by
        apply Fin.ext
        simpa using congrArg Fin.val hx
      calc
        mggEncode hm (⟨0, hm⟩, (mggDecode hm v).2)
            = mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) := by rw [hx0]
          _ = v := mggEncode_decode hm v
    · refine Or.inr ?_
      refine mem_image.mpr ⟨(mggDecode hm v).1, mem_univ _, ?_⟩
      have hy0 : (mggDecode hm v).2 = ⟨0, hm⟩ := by
        apply Fin.ext
        simpa using congrArg Fin.val hy
      calc
        mggEncode hm ((mggDecode hm v).1, ⟨0, hm⟩)
            = mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) := by rw [hy0]
          _ = v := mggEncode_decode hm v
  · intro hv
    apply (mem_mggAxis_iff hm v).mpr
    rcases mem_union.mp hv with h | h
    · obtain ⟨y, _, rfl⟩ := mem_image.mp (show v ∈ mggRow0 m hm from h)
      exact Or.inl (by simp [mggDecode_encode])
    · obtain ⟨x, _, rfl⟩ := mem_image.mp (show v ∈ mggCol0 m hm from h)
      exact Or.inr (by simp [mggDecode_encode])

/-- Safe axis bound `|A_m| ≤ 2m` (exact is `2m-1`; union bound suffices for density). -/
theorem mggAxis_card_le {m : ℕ} (hm : 0 < m) :
    (mggAxis m hm).card ≤ 2 * m := by
  rw [mggAxis_eq_row0_union_col0 hm]
  calc
    (mggRow0 m hm ∪ mggCol0 m hm).card
        ≤ (mggRow0 m hm).card + (mggCol0 m hm).card := card_union_le _ _
    _ = m + m := by rw [mggRow0_card hm, mggCol0_card hm]
    _ = 2 * m := by ring

/-- At the informative floor, `3 |A| ≤ m²` using `|A| ≤ 2m` and `m ≥ 6`. -/
theorem mggAxis_card_mul_three_le_sq {m : ℕ} (hm0 : 0 < m)
    (hm : mggInformativeFloor ≤ m) :
    3 * (mggAxis m hm0).card ≤ m * m := by
  have hle := mggAxis_card_le hm0
  have h6 : 6 ≤ m := hm
  calc
    3 * (mggAxis m hm0).card ≤ 3 * (2 * m) := Nat.mul_le_mul_left 3 hle
    _ = 6 * m := by ring
    _ ≤ m * m := by
      have := Nat.mul_le_mul_left m h6
      simpa [Nat.mul_comm 6] using this

theorem mggNeighbor_S_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggS =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).1 + (mggDecode hm v).2) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_Sinv_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggSinv =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2 - (mggDecode hm v).1) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_T_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggT =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1 + (mggDecode hm v).2, (mggDecode hm v).2) := by
  letI : NeZero m := mggNeZero hm
  rfl

theorem mggNeighbor_Tinv_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggTinv =
      letI : NeZero m := mggNeZero hm
      mggEncode hm ((mggDecode hm v).1 - (mggDecode hm v).2, (mggDecode hm v).2) := by
  letI : NeZero m := mggNeZero hm
  rfl

/-- `S` loops exactly on the vertical axis `x = 0`. -/
theorem mggNeighbor_S_eq_self_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggS = v ↔
      letI : NeZero m := mggNeZero hm
      (mggDecode hm v).1 = 0 := by
  letI : NeZero m := mggNeZero hm
  constructor
  · intro h
    have h' : mggDecode hm (mggNeighbor hm v mggS) = mggDecode hm v :=
      congrArg (mggDecode hm) h
    rw [mggNeighbor_S_eq hm v, mggDecode_encode] at h'
    exact add_eq_right.mp (Prod.ext_iff.mp h').2
  · intro hx
    calc
      mggNeighbor hm v mggS
          = mggEncode hm ((mggDecode hm v).1,
              (mggDecode hm v).1 + (mggDecode hm v).2) := mggNeighbor_S_eq hm v
      _ = mggEncode hm (0, 0 + (mggDecode hm v).2) := by rw [hx]
      _ = mggEncode hm (0, (mggDecode hm v).2) := by simp
      _ = mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) := by rw [hx]
      _ = v := mggEncode_decode hm v

/-- `S⁻¹` loops exactly on `x = 0`. -/
theorem mggNeighbor_Sinv_eq_self_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggSinv = v ↔
      letI : NeZero m := mggNeZero hm
      (mggDecode hm v).1 = 0 := by
  letI : NeZero m := mggNeZero hm
  constructor
  · intro h
    have h' : mggDecode hm (mggNeighbor hm v mggSinv) = mggDecode hm v :=
      congrArg (mggDecode hm) h
    rw [mggNeighbor_Sinv_eq hm v, mggDecode_encode] at h'
    exact sub_eq_self.mp (Prod.ext_iff.mp h').2
  · intro hx
    calc
      mggNeighbor hm v mggSinv
          = mggEncode hm ((mggDecode hm v).1,
              (mggDecode hm v).2 - (mggDecode hm v).1) := mggNeighbor_Sinv_eq hm v
      _ = mggEncode hm (0, (mggDecode hm v).2 - 0) := by rw [hx]
      _ = mggEncode hm (0, (mggDecode hm v).2) := by simp
      _ = mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) := by rw [hx]
      _ = v := mggEncode_decode hm v

/-- `T` loops exactly on the horizontal axis `y = 0`. -/
theorem mggNeighbor_T_eq_self_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggT = v ↔
      letI : NeZero m := mggNeZero hm
      (mggDecode hm v).2 = 0 := by
  letI : NeZero m := mggNeZero hm
  constructor
  · intro h
    have h' : mggDecode hm (mggNeighbor hm v mggT) = mggDecode hm v :=
      congrArg (mggDecode hm) h
    rw [mggNeighbor_T_eq hm v, mggDecode_encode] at h'
    exact add_eq_left.mp (Prod.ext_iff.mp h').1
  · intro hy
    calc
      mggNeighbor hm v mggT
          = mggEncode hm ((mggDecode hm v).1 + (mggDecode hm v).2,
              (mggDecode hm v).2) := mggNeighbor_T_eq hm v
      _ = mggEncode hm ((mggDecode hm v).1 + 0, 0) := by rw [hy]
      _ = mggEncode hm ((mggDecode hm v).1, 0) := by simp
      _ = mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) := by rw [hy]
      _ = v := mggEncode_decode hm v

/-- `T⁻¹` loops exactly on `y = 0`. -/
theorem mggNeighbor_Tinv_eq_self_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggNeighbor hm v mggTinv = v ↔
      letI : NeZero m := mggNeZero hm
      (mggDecode hm v).2 = 0 := by
  letI : NeZero m := mggNeZero hm
  constructor
  · intro h
    have h' : mggDecode hm (mggNeighbor hm v mggTinv) = mggDecode hm v :=
      congrArg (mggDecode hm) h
    rw [mggNeighbor_Tinv_eq hm v, mggDecode_encode] at h'
    exact sub_eq_self.mp (Prod.ext_iff.mp h').1
  · intro hy
    calc
      mggNeighbor hm v mggTinv
          = mggEncode hm ((mggDecode hm v).1 - (mggDecode hm v).2,
              (mggDecode hm v).2) := mggNeighbor_Tinv_eq hm v
      _ = mggEncode hm ((mggDecode hm v).1 - 0, 0) := by rw [hy]
      _ = mggEncode hm ((mggDecode hm v).1, 0) := by simp
      _ = mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) := by rw [hy]
      _ = v := mggEncode_decode hm v

/-- Any self-neighbor under a shear generator lies on the axis. -/
theorem mggNeighbor_shear_loop_mem_axis {m : ℕ} (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggShearGens)
    (hloop : mggNeighbor hm v s = v) :
    v ∈ mggAxis m hm := by
  letI : NeZero m := mggNeZero hm
  simp only [mggShearGens, mem_insert, mem_singleton] at hs
  apply (mem_mggAxis_iff hm v).mpr
  rcases hs with hs | hs | hs | hs
  · subst hs; exact Or.inl ((mggNeighbor_S_eq_self_iff hm v).mp hloop)
  · subst hs; exact Or.inl ((mggNeighbor_Sinv_eq_self_iff hm v).mp hloop)
  · subst hs; exact Or.inr ((mggNeighbor_T_eq_self_iff hm v).mp hloop)
  · subst hs; exact Or.inr ((mggNeighbor_Tinv_eq_self_iff hm v).mp hloop)

/-- Labeled multi-cut size: generator incidences leaving `S`. -/
def mggMultiCutCard {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) : ℕ :=
  ∑ v ∈ S, ((Finset.univ : Finset (Fin 8)).filter fun s =>
    mggNeighbor hm v s ∉ S).card

theorem mggMultiCutCard_eq_sum {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    mggMultiCutCard hm S =
      ∑ v ∈ S, ((Finset.univ : Finset (Fin 8)).filter fun s =>
        mggNeighbor hm v s ∉ S).card :=
  rfl

/-- For `1 < m`, a self-neighbor forces a shear generator. -/
theorem mggNeighbor_eq_self_mem_shear {m : ℕ} (hm : 1 < m) (v : Fin (m * m))
    {s : Fin 8} (hloop : mggNeighbor (lt_trans Nat.zero_lt_one hm) v s = v) :
    s ∈ mggShearGens := by
  have hnR := mggNeighbor_right_ne hm v
  have hnL := mggNeighbor_left_ne hm v
  have hnU := mggNeighbor_up_ne hm v
  have hnD := mggNeighbor_down_ne hm v
  fin_cases s
  · exact False.elim (hnR (by simpa [mggRight] using hloop))
  · exact False.elim (hnL (by simpa [mggLeft] using hloop))
  · exact False.elim (hnU (by simpa [mggUp] using hloop))
  · exact False.elim (hnD (by simpa [mggDown] using hloop))
  · simp [mggShearGens, mggS]
  · simp [mggShearGens, mggSinv]
  · simp [mggShearGens, mggT]
  · simp [mggShearGens, mggTinv]

/-- Off the axis, no generator loops when `1 < m`. -/
theorem mggNeighbor_ne_self_of_not_mem_axis {m : ℕ} (hm : 1 < m) (v : Fin (m * m))
    (hax : v ∉ mggAxis m (lt_trans Nat.zero_lt_one hm)) (s : Fin 8) :
    mggNeighbor (lt_trans Nat.zero_lt_one hm) v s ≠ v := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  intro hloop
  exact hax (mggNeighbor_shear_loop_mem_axis hm0 v
    (mggNeighbor_eq_self_mem_shear hm v hloop) hloop)

/-- Loop incidences inside `S` charge to the axis (at most 4 per axis vertex). -/
theorem mgg_loop_incidences_le_four_mul_axis {m : ℕ} (hm : 1 < m)
    (S : Finset (Fin (m * m))) :
    (∑ v ∈ S, ((Finset.univ : Finset (Fin 8)).filter fun s =>
        mggNeighbor (lt_trans Nat.zero_lt_one hm) v s = v).card) ≤
      4 * (S ∩ mggAxis m (lt_trans Nat.zero_lt_one hm)).card := by
  classical
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  have hterm : ∀ v ∈ S,
      ((Finset.univ : Finset (Fin 8)).filter fun s =>
        mggNeighbor hm0 v s = v).card ≤
        4 * (if v ∈ mggAxis m hm0 then 1 else 0) := by
    intro v _
    by_cases hax : v ∈ mggAxis m hm0
    · simp only [hax, ↓reduceIte, mul_one]
      have hsub :
          ((Finset.univ : Finset (Fin 8)).filter fun s =>
            mggNeighbor hm0 v s = v) ⊆ mggShearGens := by
        intro s hs
        exact mggNeighbor_eq_self_mem_shear hm v (by simpa [mem_filter] using hs)
      exact (card_le_card hsub).trans (le_of_eq mggShearGens_card)
    · simp only [hax, ↓reduceIte, mul_zero]
      refine le_of_eq ?_
      have hempty :
          ((Finset.univ : Finset (Fin 8)).filter fun s =>
            mggNeighbor hm0 v s = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro s _
        exact mggNeighbor_ne_self_of_not_mem_axis hm v hax s
      simp [hempty]
  have hsum := Finset.sum_le_sum hterm
  have haxis :
      (∑ v ∈ S, 4 * (if v ∈ mggAxis m hm0 then 1 else 0)) =
        4 * (S ∩ mggAxis m hm0).card := by
    have hrewrite :
        (∑ v ∈ S, 4 * (if v ∈ mggAxis m hm0 then 1 else 0)) =
          ∑ v ∈ S, (if v ∈ mggAxis m hm0 then (4 : ℕ) else 0) :=
      Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
    have h' :
        (∑ v ∈ S, (if v ∈ mggAxis m hm0 then (4 : ℕ) else 0)) =
          (S ∩ mggAxis m hm0).card * 4 := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
        nsmul_eq_mul, mul_zero, add_zero, Finset.filter_mem_eq_inter]
      norm_cast
    rw [hrewrite, h', Nat.mul_comm]
  exact hsum.trans (le_of_eq haxis)

/-- Nat witness for Gabber Galil Cheeger slack: `5√2 < 71/10` via squares. -/
theorem mgg_gabber_galil_cheeger_nat_witness : 50 * 100 < 71 * 71 := by
  decide

/-- From multi expansion `2|S| ≤ 5|∂_M S|` conclude Inv-3 on the multi cut. -/
theorem mgg_card_le_three_mul_of_two_fifth {s c : ℕ}
    (h : 2 * s ≤ 5 * c) : s ≤ 3 * c := by
  omega

/-- Inv-4 absorption: from `|S| ≤ 3(|∂_G|+loss)` and `12·loss ≤ |S|` get `|S| ≤ 4|∂_G|`. -/
theorem mgg_inv4_absorb_of_loss_le_twelfth {s g loss : ℕ}
    (hmain : s ≤ 3 * (g + loss)) (hloss : 12 * loss ≤ s) : s ≤ 4 * g := by
  have h4 : 4 * s ≤ 12 * g + 12 * loss := by
    calc
      4 * s ≤ 4 * (3 * (g + loss)) := Nat.mul_le_mul_left 4 hmain
      _ = 12 * g + 12 * loss := by ring
  omega

namespace MGGFrontier

/-- Gabber Galil style Inv on every informative simple MGG (spectral gap open). -/
theorem mggGraph_hasExpansionInv (m : ℕ) (hm0 : 0 < m)
    (hm : mggInformativeFloor ≤ m) :
    HasExpansionInv (mggGraph m hm0) mggInvK := by
  sorry

/-- Intermediate Block A pin: unbounded simple MGG Inv expanders (no regularity).
Discharges connectivity via packaging; open content is `mggGraph_hasExpansionInv`. -/
theorem exists_mgg_simple_hasExpansionInv_family :
    ∀ N : ℕ, ∃ (m : ℕ) (hm : 0 < m),
      max N mggInformativeFloor ≤ m ∧
        (mggGraph m hm).IsConnected ∧
          HasExpansionInv (mggGraph m hm) mggInvK :=
  exists_mgg_simple_hasExpansionInv_family_of_inv mggGraph_hasExpansionInv

end MGGFrontier

end SATurday.ProofComplexity

