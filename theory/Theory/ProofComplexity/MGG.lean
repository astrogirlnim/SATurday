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

/-! ## Cluster 31: multi-cut to simple edgeBoundary transfer

Cluster 30 landed axis loops and `mggMultiCutCard`. This cluster relates the
labeled multi-cut to `edgeBoundary (mggGraph …)` via Cayley inverse generators
and leaving pairs, proving `|∂_G S| ≤ |∂_M S|`. Tighter axis loss and spectral
input remain for later clusters. -/

/-- Inverse generator index: undoes one labeled MGG step. -/
def mggInvGen (s : Fin 8) : Fin 8 :=
  match s.val with
  | 0 => mggLeft
  | 1 => mggRight
  | 2 => mggDown
  | 3 => mggUp
  | 4 => mggSinv
  | 5 => mggS
  | 6 => mggTinv
  | _ => mggT

theorem mggInvGen_right : mggInvGen mggRight = mggLeft := rfl
theorem mggInvGen_left : mggInvGen mggLeft = mggRight := rfl
theorem mggInvGen_up : mggInvGen mggUp = mggDown := rfl
theorem mggInvGen_down : mggInvGen mggDown = mggUp := rfl
theorem mggInvGen_S : mggInvGen mggS = mggSinv := rfl
theorem mggInvGen_Sinv : mggInvGen mggSinv = mggS := rfl
theorem mggInvGen_T : mggInvGen mggT = mggTinv := rfl
theorem mggInvGen_Tinv : mggInvGen mggTinv = mggT := rfl

/-- Involution on generator labels. -/
theorem mggInvGen_invGen (s : Fin 8) : mggInvGen (mggInvGen s) = s := by
  fin_cases s <;> rfl

/-- Neighbor step then inverse recovers the start vertex. -/
theorem mggNeighbor_invGen {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    mggNeighbor hm (mggNeighbor hm v s) (mggInvGen s) = v := by
  letI : NeZero m := mggNeZero hm
  fin_cases s
  · change mggNeighbor hm (mggNeighbor hm v mggRight) mggLeft = v
    rw [mggNeighbor_right_eq, mggNeighbor_left_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggLeft) mggRight = v
    rw [mggNeighbor_left_eq, mggNeighbor_right_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggUp) mggDown = v
    rw [mggNeighbor_up_eq, mggNeighbor_down_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggDown) mggUp = v
    rw [mggNeighbor_down_eq, mggNeighbor_up_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggS) mggSinv = v
    rw [mggNeighbor_S_eq, mggNeighbor_Sinv_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggSinv) mggS = v
    rw [mggNeighbor_Sinv_eq, mggNeighbor_S_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggT) mggTinv = v
    rw [mggNeighbor_T_eq, mggNeighbor_Tinv_eq, mggDecode_encode]
    simp [mggEncode_decode]
  · change mggNeighbor hm (mggNeighbor hm v mggTinv) mggT = v
    rw [mggNeighbor_Tinv_eq, mggNeighbor_T_eq, mggDecode_encode]
    simp [mggEncode_decode]

/-- Leaving labeled incidences as a Finset of pairs. -/
def mggLeavingPairs {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin (m * m) × Fin 8) :=
  (S.product (Finset.univ : Finset (Fin 8))).filter fun p =>
    mggNeighbor hm p.1 p.2 ∉ S

theorem mem_mggLeavingPairs_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin (m * m) × Fin 8) :
    p ∈ mggLeavingPairs hm S ↔ p.1 ∈ S ∧ mggNeighbor hm p.1 p.2 ∉ S := by
  simp [mggLeavingPairs, mem_product]

theorem mggLeavingPairs_card {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (mggLeavingPairs hm S).card = mggMultiCutCard hm S := by
  classical
  simp only [mggLeavingPairs, mggMultiCutCard]
  change ((S ×ˢ (univ : Finset (Fin 8))).filter
      fun p => mggNeighbor hm p.1 p.2 ∉ S).card =
    ∑ v ∈ S, ((univ : Finset (Fin 8)).filter fun s => mggNeighbor hm v s ∉ S).card
  rw [card_eq_sum_ones, sum_filter, sum_product]
  exact sum_congr rfl fun v _ => by
    rw [card_eq_sum_ones, sum_filter]

/-- A neighbor outside `S` cannot equal a vertex inside `S`. -/
theorem mggNeighbor_ne_of_mem_not_mem {m : ℕ} {S : Finset (Fin (m * m))}
    {v w : Fin (m * m)} (hv : v ∈ S) (hw : w ∉ S) : v ≠ w :=
  fun h => hw (h ▸ hv)

/-- Non-loop neighbor yields adjacency in the simple graph. -/
theorem mgg_adj_of_neighbor_ne {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8)
    (hne : mggNeighbor hm v s ≠ v) :
    (mggGraph m hm).Adj v (mggNeighbor hm v s) := by
  obtain ⟨e, he, hends⟩ := mggEdgeOf_eq_some_of_ne hm v s hne
  refine ⟨e, mem_mggGraph_of_edgeOf hm v s he, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Leaving non-loop incidence produces a concrete cut edge. -/
theorem mggEdgeOf_eq_some_mem_edgeBoundary_of_leaving {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S) (s : Fin 8)
    (hw : mggNeighbor hm v s ∉ S) :
    ∃ e, mggEdgeOf hm v s = some e ∧ e ∈ edgeBoundary (mggGraph m hm) S := by
  have hne : mggNeighbor hm v s ≠ v :=
    (mggNeighbor_ne_of_mem_not_mem hv hw).symm
  obtain ⟨e, he, hends⟩ := mggEdgeOf_eq_some_of_ne hm v s hne
  refine ⟨e, he, ?_⟩
  refine (mem_edgeBoundary_iff).mpr ⟨mem_mggGraph_of_edgeOf hm v s he, ?_⟩
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1 ▸ hv, h2 ▸ hw⟩
  · exact Or.inr ⟨h1 ▸ hw, h2 ▸ hv⟩

/-- Every edge of the simple MGG arises from some labeled `mggEdgeOf`. -/
theorem exists_mggEdgeOf_eq_some_of_mem {m : ℕ} (hm : 0 < m)
    {e : FinEdge (m * m)} (he : e ∈ mggGraph m hm) :
    ∃ (v : Fin (m * m)) (s : Fin 8), mggEdgeOf hm v s = some e := by
  obtain ⟨v, _, hs⟩ := mem_biUnion.mp he
  obtain ⟨s, _, hcell⟩ := mem_biUnion.mp hs
  cases h : mggEdgeOf hm v s with
  | none =>
    have : e ∈ (∅ : Finset (FinEdge (m * m))) := by simpa [h] using hcell
    exact (notMem_empty e this).elim
  | some e' =>
    have : e ∈ ({e'} : Finset (FinEdge (m * m))) := by simpa [h] using hcell
    have hee' : e = e' := mem_singleton.mp this
    exact ⟨v, s, by rw [h, hee']⟩

/-- Endpoints of a realized `mggEdgeOf` are `v` and its neighbor. -/
theorem mggEdgeOf_eq_some_endpoints {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (s : Fin 8) {e : FinEdge (m * m)}
    (he : mggEdgeOf hm v s = some e) :
    (e.val.1 = v ∧ e.val.2 = mggNeighbor hm v s) ∨
      (e.val.1 = mggNeighbor hm v s ∧ e.val.2 = v) := by
  have hne : mggNeighbor hm v s ≠ v := by
    intro hloop
    simp [mggEdgeOf, hloop] at he
  obtain ⟨e', he', hends⟩ := mggEdgeOf_eq_some_of_ne hm v s hne
  have : e' = e := by
    rw [he'] at he; exact Option.some_injective _ he
  subst this
  exact hends

/-- Same undirected edge from the inverse generator at the neighbor. -/
theorem mggEdgeOf_invGen_eq_of_eq_some {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (s : Fin 8) {e : FinEdge (m * m)}
    (he : mggEdgeOf hm v s = some e) :
    mggEdgeOf hm (mggNeighbor hm v s) (mggInvGen s) = some e := by
  have hends := mggEdgeOf_eq_some_endpoints hm v s he
  set w := mggNeighbor hm v s
  have hback : mggNeighbor hm w (mggInvGen s) = v := mggNeighbor_invGen hm v s
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hvw : v.val < w.val := by
      have := e.property
      simp only [h1, h2] at this
      exact this
    have hnw : ¬ w.val < v.val := Nat.not_lt_of_le (Nat.le_of_lt hvw)
    have heq : e = ⟨(v, w), hvw⟩ := Subtype.ext (Prod.ext h1 h2)
    rw [heq, mggEdgeOf, hback, dif_neg hnw, dif_pos hvw]
  · have hwv : w.val < v.val := by
      have := e.property
      simp only [h1, h2] at this
      exact this
    have heq : e = ⟨(w, v), hwv⟩ := Subtype.ext (Prod.ext h1 h2)
    rw [heq, mggEdgeOf, hback, dif_pos hwv]

/-- Every simple cut edge is witnessed by at least one leaving labeled pair. -/
theorem exists_mem_mggLeavingPairs_of_mem_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) {e : FinEdge (m * m)}
    (he : e ∈ edgeBoundary (mggGraph m hm) S) :
    ∃ p ∈ mggLeavingPairs hm S, mggEdgeOf hm p.1 p.2 = some e := by
  obtain ⟨heG, hcut⟩ := (mem_edgeBoundary_iff).mp he
  obtain ⟨v, s, hvs⟩ := exists_mggEdgeOf_eq_some_of_mem hm heG
  have hends := mggEdgeOf_eq_some_endpoints hm v s hvs
  set w := mggNeighbor hm v s
  rcases hends with ⟨he1, he2⟩ | ⟨he1, he2⟩
  · rcases hcut with ⟨h1S, h2n⟩ | ⟨h1n, h2S⟩
    · refine ⟨(v, s), (mem_mggLeavingPairs_iff hm S _).mpr ⟨?_, ?_⟩, hvs⟩
      · simpa [he1] using h1S
      · simpa [he2] using h2n
    · have hinv := mggEdgeOf_invGen_eq_of_eq_some hm v s hvs
      refine ⟨(w, mggInvGen s), (mem_mggLeavingPairs_iff hm S _).mpr ⟨?_, ?_⟩, ?_⟩
      · simpa [he2] using h2S
      · rw [show mggNeighbor hm w (mggInvGen s) = v from mggNeighbor_invGen hm v s]
        simpa [he1] using h1n
      · simpa [w] using hinv
  · rcases hcut with ⟨h1S, h2n⟩ | ⟨h1n, h2S⟩
    · have hinv := mggEdgeOf_invGen_eq_of_eq_some hm v s hvs
      refine ⟨(w, mggInvGen s), (mem_mggLeavingPairs_iff hm S _).mpr ⟨?_, ?_⟩, ?_⟩
      · simpa [he1] using h1S
      · rw [show mggNeighbor hm w (mggInvGen s) = v from mggNeighbor_invGen hm v s]
        simpa [he2] using h2n
      · simpa [w] using hinv
    · refine ⟨(v, s), (mem_mggLeavingPairs_iff hm S _).mpr ⟨?_, ?_⟩, hvs⟩
      · simpa [he2] using h2S
      · simpa [he1] using h1n

/-- Chosen leaving witness for a cut edge. -/
noncomputable def mggLeavingWitness {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) {e : FinEdge (m * m)}
    (he : e ∈ edgeBoundary (mggGraph m hm) S) : Fin (m * m) × Fin 8 :=
  Classical.choose (exists_mem_mggLeavingPairs_of_mem_edgeBoundary hm S he)

theorem mggLeavingWitness_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) {e : FinEdge (m * m)}
    (he : e ∈ edgeBoundary (mggGraph m hm) S) :
    mggLeavingWitness hm S he ∈ mggLeavingPairs hm S :=
  (Classical.choose_spec (exists_mem_mggLeavingPairs_of_mem_edgeBoundary hm S he)).1

theorem mggLeavingWitness_edgeOf {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) {e : FinEdge (m * m)}
    (he : e ∈ edgeBoundary (mggGraph m hm) S) :
    mggEdgeOf hm (mggLeavingWitness hm S he).1 (mggLeavingWitness hm S he).2 =
      some e :=
  (Classical.choose_spec (exists_mem_mggLeavingPairs_of_mem_edgeBoundary hm S he)).2

/-- Simple cut is at most the labeled multi-cut: `|∂_G S| ≤ |∂_M S|`. -/
theorem edgeBoundary_card_le_mggMultiCutCard {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (edgeBoundary (mggGraph m hm) S).card ≤ mggMultiCutCard hm S := by
  classical
  rw [← mggLeavingPairs_card hm S]
  have h :=
    card_le_card_of_injOn
      (s := (edgeBoundary (mggGraph m hm) S).attach)
      (t := mggLeavingPairs hm S)
      (fun e => mggLeavingWitness hm S e.property)
      (fun e _ => mggLeavingWitness_mem hm S e.property)
      (fun e₁ _ e₂ _ h => by
        have h1 := mggLeavingWitness_edgeOf hm S e₁.property
        have h2 := mggLeavingWitness_edgeOf hm S e₂.property
        have h1' :
            mggEdgeOf hm (mggLeavingWitness hm S e₂.property).1
              (mggLeavingWitness hm S e₂.property).2 = some (e₁ : FinEdge (m * m)) := by
          simpa [h] using h1
        exact Subtype.ext (Option.some_injective _ (h1'.symm.trans h2)))
  simpa [card_attach] using h

/-! ## Cluster 32: reverse cut loss decomposition

Cluster 31 gave `|∂_G S| ≤ |∂_M S|`. Inv-4 absorb needs
`|∂_M S| ≤ |∂_G S| + loss(S)`. This cluster defines labeled leaving excess,
proves `|∂_M| = ∑ outNeighbors + reverseLoss` and
`|∂_M| ≤ |∂_G| + reverseLoss`, and lands `excess ≤ 4` for `m ≥ 3`.
Axis-aware tightening and spectral or Cheeger input remain later. -/

/-- Leaving generator labels at `v` relative to `S`. -/
def mggLeavingGens {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : Finset (Fin 8) :=
  (univ : Finset (Fin 8)).filter fun s => mggNeighbor hm v s ∉ S

theorem mem_mggLeavingGens_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (s : Fin 8) :
    s ∈ mggLeavingGens hm S v ↔ mggNeighbor hm v s ∉ S := by
  simp [mggLeavingGens]

theorem mggLeavingGens_card_sum {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (∑ v ∈ S, (mggLeavingGens hm S v).card) = mggMultiCutCard hm S := by
  simp only [mggLeavingGens, mggMultiCutCard]

/-- Distinct outside neighbors reachable by a labeled generator from `v`. -/
def mggOutNeighbors {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : Finset (Fin (m * m)) :=
  (mggLeavingGens hm S v).image fun s => mggNeighbor hm v s

theorem mem_mggOutNeighbors_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m)) :
    w ∈ mggOutNeighbors hm S v ↔
      ∃ s : Fin 8, mggNeighbor hm v s = w ∧ w ∉ S := by
  constructor
  · intro hw
    obtain ⟨s, hsL, rfl⟩ := mem_image.mp hw
    exact ⟨s, rfl, (mem_mggLeavingGens_iff hm S v s).mp hsL⟩
  · rintro ⟨s, rfl, hsn⟩
    exact mem_image.mpr ⟨s, (mem_mggLeavingGens_iff hm S v s).mpr hsn, rfl⟩

/-- Parallel leaving excess at `v`. -/
def mggLeavingExcess {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : ℕ :=
  (mggLeavingGens hm S v).card - (mggOutNeighbors hm S v).card

theorem mggOutNeighbors_card_le_leavingGens {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    (mggOutNeighbors hm S v).card ≤ (mggLeavingGens hm S v).card :=
  card_image_le

theorem mggLeavingGens_card_eq_out_add_excess {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    (mggLeavingGens hm S v).card =
      (mggOutNeighbors hm S v).card + mggLeavingExcess hm S v := by
  simp only [mggLeavingExcess]
  rw [add_comm]
  exact (Nat.sub_add_cancel (mggOutNeighbors_card_le_leavingGens hm S v)).symm

/-- Total reverse cut loss over `S`. -/
def mggReverseCutLoss {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) : ℕ :=
  ∑ v ∈ S, mggLeavingExcess hm S v

theorem mggMultiCutCard_eq_sum_out_add_reverseLoss {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggMultiCutCard hm S =
      (∑ v ∈ S, (mggOutNeighbors hm S v).card) + mggReverseCutLoss hm S := by
  classical
  have hsum :=
    (sum_congr (s₁ := S) (s₂ := S) rfl
      fun v _ => mggLeavingGens_card_eq_out_add_excess hm S v)
  calc
    mggMultiCutCard hm S = ∑ v ∈ S, (mggLeavingGens hm S v).card :=
      (mggLeavingGens_card_sum hm S).symm
    _ = ∑ v ∈ S,
          ((mggOutNeighbors hm S v).card + mggLeavingExcess hm S v) := hsum
    _ = (∑ v ∈ S, (mggOutNeighbors hm S v).card) +
          ∑ v ∈ S, mggLeavingExcess hm S v := sum_add_distrib
    _ = (∑ v ∈ S, (mggOutNeighbors hm S v).card) + mggReverseCutLoss hm S :=
      rfl

/-- Four translation generators. -/
def mggTranslationGens : Finset (Fin 8) :=
  {mggRight, mggLeft, mggUp, mggDown}

theorem mggTranslationGens_card : mggTranslationGens.card = 4 := by decide

theorem mem_mggTranslationGens_iff (s : Fin 8) :
    s ∈ mggTranslationGens ↔
      s = mggRight ∨ s = mggLeft ∨ s = mggUp ∨ s = mggDown := by
  fin_cases s <;> decide

/-- Translation neighbors at a fixed vertex are pairwise distinct for `m ≥ 3`. -/
theorem mggNeighbor_translation_injOn {m : ℕ} (hm : 3 ≤ m) (v : Fin (m * m)) :
    Set.InjOn (mggNeighbor (lt_of_lt_of_le (by decide : 0 < 3) hm) v)
      (mggTranslationGens : Set (Fin 8)) := by
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 3) hm
  intro s hs t ht hst
  have hs' := (mem_mggTranslationGens_iff s).mp (by simpa using hs)
  have ht' := (mem_mggTranslationGens_iff t).mp (by simpa using ht)
  rcases hs' with hR | hL | hU | hD <;> rcases ht' with hR' | hL' | hU' | hD' <;>
    (try subst s; try subst t)
  · rfl
  · exact (mggNeighbor_right_ne_left hm v hst).elim
  · exact (mggNeighbor_right_ne_up hm1 v hst).elim
  · exact (mggNeighbor_right_ne_down hm1 v hst).elim
  · exact (mggNeighbor_right_ne_left hm v hst.symm).elim
  · rfl
  · exact (mggNeighbor_left_ne_up hm1 v hst).elim
  · exact (mggNeighbor_left_ne_down hm1 v hst).elim
  · exact (mggNeighbor_right_ne_up hm1 v hst.symm).elim
  · exact (mggNeighbor_left_ne_up hm1 v hst.symm).elim
  · rfl
  · exact (mggNeighbor_up_ne_down hm v hst).elim
  · exact (mggNeighbor_right_ne_down hm1 v hst.symm).elim
  · exact (mggNeighbor_left_ne_down hm1 v hst.symm).elim
  · exact (mggNeighbor_up_ne_down hm v hst.symm).elim
  · rfl

/-- Leaving excess is at most 4 when translations inject (`m ≥ 3`). -/
theorem mggLeavingExcess_le_four {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    mggLeavingExcess (lt_of_lt_of_le (by decide : 0 < 3) hm) S v ≤ 4 := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  set L := mggLeavingGens hm0 S v
  set T := mggTranslationGens ∩ L
  have hTle : T.card ≤ (mggOutNeighbors hm0 S v).card := by
    have himg :
        T.image (mggNeighbor hm0 v) ⊆ mggOutNeighbors hm0 S v := by
      intro w hw
      obtain ⟨s, hsT, rfl⟩ := mem_image.mp hw
      exact mem_image.mpr ⟨s, (mem_inter.mp hsT).2, rfl⟩
    have hinj : Set.InjOn (mggNeighbor hm0 v) (T : Set (Fin 8)) :=
      (mggNeighbor_translation_injOn hm v).mono fun s hs => (mem_inter.mp hs).1
    have : T.card = (T.image (mggNeighbor hm0 v)).card :=
      (card_image_of_injOn hinj).symm
    exact (le_of_eq this).trans (card_le_card himg)
  have hsplit : L.card = T.card + (L \ mggTranslationGens).card := by
    rw [← card_inter_add_card_sdiff L mggTranslationGens, inter_comm]
  have hshear : (L \ mggTranslationGens).card ≤ 4 := by
    have hUT : (univ : Finset (Fin 8)) \ mggTranslationGens = mggShearGens := by
      decide
    have hsub : L \ mggTranslationGens ⊆
        (univ : Finset (Fin 8)) \ mggTranslationGens :=
      sdiff_subset_sdiff (subset_univ L) (Subset.rfl)
    rw [hUT] at hsub
    exact (card_le_card hsub).trans (le_of_eq mggShearGens_card)
  have hLout :
      L.card - (mggOutNeighbors hm0 S v).card ≤
        (L \ mggTranslationGens).card := by
    have hsub : T.card ≤ (mggOutNeighbors hm0 S v).card := hTle
    have hLT : L.card - T.card = (L \ mggTranslationGens).card := by
      omega
    have : L.card - (mggOutNeighbors hm0 S v).card ≤ L.card - T.card :=
      Nat.sub_le_sub_left hsub _
    exact this.trans (le_of_eq hLT)
  simpa [mggLeavingExcess, L] using hLout.trans hshear

theorem mggReverseCutLoss_le_four_mul_card {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggReverseCutLoss (lt_of_lt_of_le (by decide : 0 < 3) hm) S ≤
      4 * S.card := by
  classical
  have hsum :=
    Finset.sum_le_sum (s := S) fun v _ => mggLeavingExcess_le_four hm S v
  have hconst : (∑ _v ∈ S, (4 : ℕ)) = 4 * S.card := by
    simp [sum_const, nsmul_eq_mul, Nat.mul_comm]
  exact hsum.trans (le_of_eq hconst)

/-- Witness generator for an out-neighbor. -/
noncomputable def mggOutNeighborWitness {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m))
    (hw : w ∈ mggOutNeighbors hm S v) : Fin 8 :=
  Classical.choose ((mem_mggOutNeighbors_iff hm S v w).mp hw)

theorem mggOutNeighborWitness_eq {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m))
    (hw : w ∈ mggOutNeighbors hm S v) :
    mggNeighbor hm v (mggOutNeighborWitness hm S v w hw) = w :=
  (Classical.choose_spec ((mem_mggOutNeighbors_iff hm S v w).mp hw)).1

theorem mggOutNeighborWitness_not_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m))
    (hw : w ∈ mggOutNeighbors hm S v) :
    w ∉ S :=
  (Classical.choose_spec ((mem_mggOutNeighbors_iff hm S v w).mp hw)).2

theorem mggEdgeOf_outNeighbor_mem_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggOutNeighbors hm S v) :
    ∃ e, mggEdgeOf hm v (mggOutNeighborWitness hm S v w hw) = some e ∧
      e ∈ edgeBoundary (mggGraph m hm) S :=
  mggEdgeOf_eq_some_mem_edgeBoundary_of_leaving hm S v hv
    (mggOutNeighborWitness hm S v w hw)
    (by simpa [mggOutNeighborWitness_eq hm S v w hw] using
      mggOutNeighborWitness_not_mem hm S v w hw)

noncomputable def mggOutEdge {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggOutNeighbors hm S v) : FinEdge (m * m) :=
  Classical.choose (mggEdgeOf_outNeighbor_mem_edgeBoundary hm S v hv w hw)

theorem mggOutEdge_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggOutNeighbors hm S v) :
    mggOutEdge hm S v hv w hw ∈ edgeBoundary (mggGraph m hm) S :=
  (Classical.choose_spec (mggEdgeOf_outNeighbor_mem_edgeBoundary hm S v hv w hw)).2

theorem mggOutEdge_eq_some {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggOutNeighbors hm S v) :
    mggEdgeOf hm v (mggOutNeighborWitness hm S v w hw) =
      some (mggOutEdge hm S v hv w hw) :=
  (Classical.choose_spec (mggEdgeOf_outNeighbor_mem_edgeBoundary hm S v hv w hw)).1

theorem mggOutEdge_endpoints {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggOutNeighbors hm S v) :
    ((mggOutEdge hm S v hv w hw).val.1 = v ∧
        (mggOutEdge hm S v hv w hw).val.2 = w) ∨
      ((mggOutEdge hm S v hv w hw).val.1 = w ∧
        (mggOutEdge hm S v hv w hw).val.2 = v) := by
  have he := mggOutEdge_eq_some hm S v hv w hw
  have hnw := mggOutNeighborWitness_eq hm S v w hw
  have hends := mggEdgeOf_eq_some_endpoints hm v
    (mggOutNeighborWitness hm S v w hw) he
  simpa [hnw] using hends

/-- Directed cut pairs `(v,w)` with `v ∈ S` and labeled out-neighbor `w`. -/
def mggDirectedCutPairs {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin (m * m) × Fin (m * m)) :=
  S.biUnion fun v => (mggOutNeighbors hm S v).image fun w => (v, w)

theorem mem_mggDirectedCutPairs_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin (m * m) × Fin (m * m)) :
    p ∈ mggDirectedCutPairs hm S ↔
      p.1 ∈ S ∧ p.2 ∈ mggOutNeighbors hm S p.1 := by
  simp only [mggDirectedCutPairs, mem_biUnion, mem_image]
  constructor
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨hv, hw⟩
  · rintro ⟨hv, hw⟩
    exact ⟨p.1, hv, p.2, hw, rfl⟩

theorem mggDirectedCutPairs_card {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (mggDirectedCutPairs hm S).card =
      ∑ v ∈ S, (mggOutNeighbors hm S v).card := by
  classical
  have hdisj :
      (S : Set (Fin (m * m))).PairwiseDisjoint fun v =>
        (mggOutNeighbors hm S v).image fun w => (v, w) := by
    intro a _ b _ hne
    refine Finset.disjoint_left.2 ?_
    intro p hpA hpB
    have ha : p.1 = a := by
      obtain ⟨w, _, hw⟩ := mem_image.mp hpA
      exact (Prod.ext_iff.mp hw).1.symm
    have hb : p.1 = b := by
      obtain ⟨w, _, hw⟩ := mem_image.mp hpB
      exact (Prod.ext_iff.mp hw).1.symm
    exact hne (ha.symm.trans hb)
  rw [mggDirectedCutPairs, card_biUnion hdisj]
  refine sum_congr rfl fun v _ =>
    card_image_of_injective _ fun _ _ h => (Prod.ext_iff.mp h).2

noncomputable def mggDirectedCutEdge {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin (m * m) × Fin (m * m))
    (hp : p ∈ mggDirectedCutPairs hm S) : FinEdge (m * m) :=
  mggOutEdge hm S p.1 ((mem_mggDirectedCutPairs_iff hm S p).mp hp).1
    p.2 ((mem_mggDirectedCutPairs_iff hm S p).mp hp).2

theorem mggDirectedCutEdge_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) {p : Fin (m * m) × Fin (m * m)}
    (hp : p ∈ mggDirectedCutPairs hm S) :
    mggDirectedCutEdge hm S p hp ∈ edgeBoundary (mggGraph m hm) S := by
  simpa [mggDirectedCutEdge] using
    mggOutEdge_mem hm S p.1 ((mem_mggDirectedCutPairs_iff hm S p).mp hp).1
      p.2 ((mem_mggDirectedCutPairs_iff hm S p).mp hp).2

theorem mggDirectedCutEdge_injective {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m)))
    {p₁ : Fin (m * m) × Fin (m * m)} (hp₁ : p₁ ∈ mggDirectedCutPairs hm S)
    {p₂ : Fin (m * m) × Fin (m * m)} (hp₂ : p₂ ∈ mggDirectedCutPairs hm S)
    (h : mggDirectedCutEdge hm S p₁ hp₁ = mggDirectedCutEdge hm S p₂ hp₂) :
    p₁ = p₂ := by
  have hv₁ := ((mem_mggDirectedCutPairs_iff hm S p₁).mp hp₁).1
  have hw₁ := ((mem_mggDirectedCutPairs_iff hm S p₁).mp hp₁).2
  have hv₂ := ((mem_mggDirectedCutPairs_iff hm S p₂).mp hp₂).1
  have hw₂ := ((mem_mggDirectedCutPairs_iff hm S p₂).mp hp₂).2
  have hw₁n := mggOutNeighborWitness_not_mem hm S p₁.1 p₁.2 hw₁
  have hw₂n := mggOutNeighborWitness_not_mem hm S p₂.1 p₂.2 hw₂
  have e1 := mggOutEdge_endpoints hm S p₁.1 hv₁ p₁.2 hw₁
  have e2 := mggOutEdge_endpoints hm S p₂.1 hv₂ p₂.2 hw₂
  have heq :
      (mggOutEdge hm S p₁.1 hv₁ p₁.2 hw₁).val =
        (mggOutEdge hm S p₂.1 hv₂ p₂.2 hw₂).val :=
    congrArg Subtype.val (by simpa [mggDirectedCutEdge] using h)
  have hv : p₁.1 = p₂.1 := by
    rcases e1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases e2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · have := congrArg Prod.fst heq; simpa [a1, b1] using this
    · have := congrArg Prod.fst heq
      simp only [a1, b1] at this
      exact (hw₂n (this ▸ hv₁)).elim
    · have := congrArg Prod.fst heq
      simp only [a1, b1] at this
      exact (hw₁n (this.symm ▸ hv₂)).elim
    · have := congrArg Prod.snd heq; simpa [a2, b2] using this
  have hw : p₁.2 = p₂.2 := by
    rcases e1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases e2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · have := congrArg Prod.snd heq; simpa [a2, b2] using this
    · have := congrArg Prod.fst heq
      simp only [a1, b1] at this
      exact (hw₂n (this ▸ hv₁)).elim
    · have := congrArg Prod.fst heq
      simp only [a1, b1] at this
      exact (hw₁n (this.symm ▸ hv₂)).elim
    · have := congrArg Prod.fst heq; simpa [a1, b1] using this
  exact Prod.ext hv hw

/-- Distinct out-neighbors inject into the simple cut. -/
theorem sum_mggOutNeighbors_card_le_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (∑ v ∈ S, (mggOutNeighbors hm S v).card) ≤
      (edgeBoundary (mggGraph m hm) S).card := by
  classical
  rw [← mggDirectedCutPairs_card hm S]
  have h :=
    card_le_card_of_injOn
      (s := (mggDirectedCutPairs hm S).attach)
      (t := edgeBoundary (mggGraph m hm) S)
      (fun p => mggDirectedCutEdge hm S p.1 p.2)
      (fun p _ => mggDirectedCutEdge_mem hm S p.2)
      (fun p₁ _ p₂ _ h =>
        Subtype.ext (mggDirectedCutEdge_injective hm S p₁.2 p₂.2 h))
  simpa [card_attach] using h

/-- Reverse cut loss inequality: `|∂_M S| ≤ |∂_G S| + reverseLoss(S)`. -/
theorem mggMultiCutCard_le_edgeBoundary_add_reverseLoss {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggMultiCutCard hm S ≤
      (edgeBoundary (mggGraph m hm) S).card + mggReverseCutLoss hm S := by
  have h := mggMultiCutCard_eq_sum_out_add_reverseLoss hm S
  have hle := sum_mggOutNeighbors_card_le_edgeBoundary hm S
  omega

/-! ## Cluster 33: axis-aware reverseLoss surface

Cluster 32 certified `reverseLoss ≤ 4|S|`, not Inv-4 absorbable by
`mgg_inv4_absorb_of_loss_le_twelfth`. Uniform off-axis excess `≤ 2` is false
(counterexample: encode`(1,1)` collapses shears into translations). This cluster
lands shear-leaving charge (excess source), a near-axis band definition with
axis inclusion, and Nat absorb helpers for loss shape `4a + 2o`. Band density
and off-band excess `≤ 2` remain the next Lean obligations. -/

/-- Leaving shear labels at `v` relative to `S`. -/
def mggShearLeavingGens {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : Finset (Fin 8) :=
  mggLeavingGens hm S v ∩ mggShearGens

theorem mem_mggShearLeavingGens_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (s : Fin 8) :
    s ∈ mggShearLeavingGens hm S v ↔
      mggNeighbor hm v s ∉ S ∧ s ∈ mggShearGens := by
  simp [mggShearLeavingGens, mggLeavingGens]

/-- Shear leaving equals leaving generators outside the translation set. -/
theorem mggShearLeavingGens_eq_sdiff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    mggShearLeavingGens hm S v =
      mggLeavingGens hm S v \ mggTranslationGens := by
  classical
  have hUT : (univ : Finset (Fin 8)) \ mggTranslationGens = mggShearGens := by
    decide
  ext s
  constructor
  · intro hs
    have hL := (mem_inter.mp hs).1
    have hSh := (mem_inter.mp hs).2
    refine mem_sdiff.mpr ⟨hL, ?_⟩
    intro hT
    have : s ∈ (univ : Finset (Fin 8)) \ mggTranslationGens := by
      simpa [hUT] using hSh
    exact (mem_sdiff.mp this).2 hT
  · intro hs
    have hL := (mem_sdiff.mp hs).1
    have hT := (mem_sdiff.mp hs).2
    refine mem_inter.mpr ⟨hL, ?_⟩
    have : s ∈ (univ : Finset (Fin 8)) \ mggTranslationGens :=
      mem_sdiff.mpr ⟨mem_univ s, hT⟩
    simpa [hUT] using this

/-- Excess is at most the number of leaving shear generators. -/
theorem mggLeavingExcess_le_shearLeavingCard {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    mggLeavingExcess (lt_of_lt_of_le (by decide : 0 < 3) hm) S v ≤
      (mggShearLeavingGens (lt_of_lt_of_le (by decide : 0 < 3) hm) S v).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  set L := mggLeavingGens hm0 S v
  set T := mggTranslationGens ∩ L
  have hTle : T.card ≤ (mggOutNeighbors hm0 S v).card := by
    have himg :
        T.image (mggNeighbor hm0 v) ⊆ mggOutNeighbors hm0 S v := by
      intro w hw
      obtain ⟨s, hsT, rfl⟩ := mem_image.mp hw
      exact mem_image.mpr ⟨s, (mem_inter.mp hsT).2, rfl⟩
    have hinj : Set.InjOn (mggNeighbor hm0 v) (T : Set (Fin 8)) :=
      (mggNeighbor_translation_injOn hm v).mono fun s hs => (mem_inter.mp hs).1
    have : T.card = (T.image (mggNeighbor hm0 v)).card :=
      (card_image_of_injOn hinj).symm
    exact (le_of_eq this).trans (card_le_card himg)
  have hsplit : L.card = T.card + (L \ mggTranslationGens).card := by
    rw [← card_inter_add_card_sdiff L mggTranslationGens, inter_comm]
  have hLout :
      L.card - (mggOutNeighbors hm0 S v).card ≤
        (L \ mggTranslationGens).card := by
    have hLT : L.card - T.card = (L \ mggTranslationGens).card := by
      lia
    exact (Nat.sub_le_sub_left hTle _).trans (le_of_eq hLT)
  have heq : (L \ mggTranslationGens).card =
      (mggShearLeavingGens hm0 S v).card := by
    rw [mggShearLeavingGens_eq_sdiff hm0 S v]
  simpa [mggLeavingExcess, L, heq] using hLout

/-- Near-axis band: a coordinate lies in `{0, 1, m-1}` (shear-translation collisions). -/
def mggNearAxis (m : ℕ) (hm : 0 < m) : Finset (Fin (m * m)) :=
  letI : NeZero m := mggNeZero hm
  (univ : Finset (Fin (m * m))).filter fun v =>
    let p := mggDecode hm v
    p.1.val ≤ 1 ∨ m ≤ p.1.val + 1 ∨ p.2.val ≤ 1 ∨ m ≤ p.2.val + 1

theorem mem_mggNearAxis_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    v ∈ mggNearAxis m hm ↔
      letI : NeZero m := mggNeZero hm
      let p := mggDecode hm v
      p.1.val ≤ 1 ∨ m ≤ p.1.val + 1 ∨ p.2.val ≤ 1 ∨ m ≤ p.2.val + 1 := by
  letI : NeZero m := mggNeZero hm
  simp [mggNearAxis]

/-- Axis is contained in the near-axis band. -/
theorem mggAxis_subset_nearAxis {m : ℕ} (hm : 0 < m) :
    mggAxis m hm ⊆ mggNearAxis m hm := by
  letI : NeZero m := mggNeZero hm
  intro v hv
  apply (mem_mggNearAxis_iff hm v).mpr
  have h := (mem_mggAxis_iff hm v).mp hv
  rcases h with hx | hy
  · exact Or.inl (by
      have : (mggDecode hm v).1.val = 0 := by
        simpa using congrArg Fin.val hx
      omega)
  · exact Or.inr (Or.inr (Or.inl (by
      have : (mggDecode hm v).2.val = 0 := by
        simpa using congrArg Fin.val hy
      omega)))

/-- Total reverse loss ≤ shear-leaving mass (axis-aware collision source). -/
theorem mggReverseCutLoss_le_sum_shearLeaving {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggReverseCutLoss (lt_of_lt_of_le (by decide : 0 < 3) hm) S ≤
      ∑ v ∈ S, (mggShearLeavingGens (lt_of_lt_of_le (by decide : 0 < 3) hm) S v).card := by
  classical
  exact Finset.sum_le_sum fun v _ => mggLeavingExcess_le_shearLeavingCard hm S v

/-- Nat absorb helper: loss of shape `4a + 2o` with twelfth budget yields Inv-4. -/
theorem mgg_inv4_absorb_of_near_loss {s g a o : ℕ}
    (hmain : s ≤ 3 * (g + (4 * a + 2 * o)))
    (hloss : 12 * (4 * a + 2 * o) ≤ s) : s ≤ 4 * g :=
  mgg_inv4_absorb_of_loss_le_twelfth hmain hloss

/-- Density form: pure `4a` loss with `a ≤ 6m` and `576 m ≤ s` absorbs to Inv-4. -/
theorem mgg_inv4_absorb_axis_budget_of_large {s g a m : ℕ}
    (hmain : s ≤ 3 * (g + 4 * a))
    (ha : a ≤ 6 * m)
    (hs : 576 * m ≤ s) : s ≤ 4 * g := by
  have hloss : 12 * (4 * a) ≤ s := by
    have h1 : 48 * a ≤ 48 * (6 * m) := Nat.mul_le_mul_left 48 ha
    have h2 : 48 * a ≤ 288 * m := by
      calc
        48 * a ≤ 48 * (6 * m) := h1
        _ = 288 * m := by ring
    have h3 : 288 * m ≤ s :=
      le_trans (Nat.mul_le_mul_right m (by decide : 288 ≤ 576)) hs
    have h48 : 48 * a ≤ s := h2.trans h3
    simpa [show 12 * (4 * a) = 48 * a from by ring] using h48
  exact mgg_inv4_absorb_of_loss_le_twelfth hmain hloss

/-! ## Cluster 34: nearAxis density bound

Cluster 33 left `|nearAxis| ≤ 6m` and off-band `excess ≤ 2` open (needed for
Inv-4 absorb shape `4a + 2o`). This cluster certifies the density bound via
coordinate band strips. Off-band excess remains the next obligation. -/

/-- Near-axis coordinates: values in `{0, 1, m-1}` on `Fin m`. -/
def mggNearAxisCoord (m : ℕ) [NeZero m] : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun i => i.val ≤ 1 ∨ m ≤ i.val + 1

theorem mem_mggNearAxisCoord_iff {m : ℕ} [NeZero m] (i : Fin m) :
    i ∈ mggNearAxisCoord m ↔ i.val ≤ 1 ∨ m ≤ i.val + 1 := by
  simp [mggNearAxisCoord]

/-- At most three near-axis coordinates. -/
theorem mggNearAxisCoord_card_le (m : ℕ) [NeZero m] :
    (mggNearAxisCoord m).card ≤ 3 := by
  classical
  let s : Finset (Fin m) :=
    {⟨0, Nat.pos_of_neZero m⟩} ∪
      (if h : 1 < m then ({⟨1, h⟩} : Finset (Fin m)) else ∅) ∪
        {⟨m - 1, Nat.sub_lt (Nat.pos_of_neZero m) (by decide : 0 < 1)⟩}
  have hsub : mggNearAxisCoord m ⊆ s := by
    intro i hi
    have hi' := (mem_mggNearAxisCoord_iff i).mp hi
    have him : i.val < m := i.isLt
    have hval : i.val = 0 ∨ i.val = 1 ∨ i.val = m - 1 := by omega
    rcases hval with h0 | h1 | hm1
    · refine mem_union_left _ (mem_union_left _ ?_)
      exact mem_singleton.mpr (Fin.ext h0)
    · refine mem_union_left _ (mem_union_right _ ?_)
      have h1m : 1 < m := by omega
      simp only [h1m, ↓reduceDIte]
      exact mem_singleton.mpr (Fin.ext h1)
    · refine mem_union_right _ ?_
      exact mem_singleton.mpr (Fin.ext hm1)
  have hsc : s.card ≤ 3 := by
    have h1 : ({⟨0, Nat.pos_of_neZero m⟩} : Finset (Fin m)).card ≤ 1 := by
      simp
    have h2 :
        ((if h : 1 < m then ({⟨1, h⟩} : Finset (Fin m)) else ∅)).card ≤ 1 := by
      split_ifs <;> simp
    have h3 :
        ({⟨m - 1, Nat.sub_lt (Nat.pos_of_neZero m) (by decide : 0 < 1)⟩} :
            Finset (Fin m)).card ≤ 1 := by
      simp
    calc
      s.card ≤
          ({⟨0, Nat.pos_of_neZero m⟩} : Finset (Fin m)).card +
            ((if h : 1 < m then ({⟨1, h⟩} : Finset (Fin m)) else ∅)).card +
              ({⟨m - 1, Nat.sub_lt (Nat.pos_of_neZero m) (by decide : 0 < 1)⟩} :
                  Finset (Fin m)).card := by
        simp only [s]
        exact (card_union_le _ _).trans
          (Nat.add_le_add_right (card_union_le _ _) _)
      _ ≤ 1 + 1 + 1 := Nat.add_le_add (Nat.add_le_add h1 h2) h3
      _ = 3 := by decide
  exact (card_le_card hsub).trans hsc

/-- Horizontal strips over near-axis first coordinates. -/
def mggNearAxisRows {m : ℕ} (hm : 0 < m) : Finset (Fin (m * m)) :=
  letI : NeZero m := mggNeZero hm
  (mggNearAxisCoord m).biUnion fun x =>
    (univ : Finset (Fin m)).image fun y => mggEncode hm (x, y)

/-- Vertical strips over near-axis second coordinates. -/
def mggNearAxisCols {m : ℕ} (hm : 0 < m) : Finset (Fin (m * m)) :=
  letI : NeZero m := mggNeZero hm
  (mggNearAxisCoord m).biUnion fun y =>
    (univ : Finset (Fin m)).image fun x => mggEncode hm (x, y)

theorem mggNearAxis_eq_rows_union_cols {m : ℕ} (hm : 0 < m) :
    mggNearAxis m hm = mggNearAxisRows hm ∪ mggNearAxisCols hm := by
  classical
  letI : NeZero m := mggNeZero hm
  ext v
  constructor
  · intro hv
    have h := (mem_mggNearAxis_iff hm v).mp hv
    rw [mem_union]
    rcases h with hx | hx | hy | hy
    · refine Or.inl (mem_biUnion.mpr ⟨(mggDecode hm v).1, ?_, ?_⟩)
      · exact (mem_mggNearAxisCoord_iff _).mpr (Or.inl hx)
      · exact mem_image.mpr ⟨(mggDecode hm v).2, mem_univ _, mggEncode_decode hm v⟩
    · refine Or.inl (mem_biUnion.mpr ⟨(mggDecode hm v).1, ?_, ?_⟩)
      · exact (mem_mggNearAxisCoord_iff _).mpr (Or.inr hx)
      · exact mem_image.mpr ⟨(mggDecode hm v).2, mem_univ _, mggEncode_decode hm v⟩
    · refine Or.inr (mem_biUnion.mpr ⟨(mggDecode hm v).2, ?_, ?_⟩)
      · exact (mem_mggNearAxisCoord_iff _).mpr (Or.inl hy)
      · exact mem_image.mpr ⟨(mggDecode hm v).1, mem_univ _, mggEncode_decode hm v⟩
    · refine Or.inr (mem_biUnion.mpr ⟨(mggDecode hm v).2, ?_, ?_⟩)
      · exact (mem_mggNearAxisCoord_iff _).mpr (Or.inr hy)
      · exact mem_image.mpr ⟨(mggDecode hm v).1, mem_univ _, mggEncode_decode hm v⟩
  · intro hv
    apply (mem_mggNearAxis_iff hm v).mpr
    rcases mem_union.mp hv with hR | hC
    · obtain ⟨x, hx, hy⟩ := mem_biUnion.mp hR
      obtain ⟨y, _, rfl⟩ := mem_image.mp hy
      have hx' := (mem_mggNearAxisCoord_iff x).mp hx
      simp [mggDecode_encode]
      rcases hx' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨y, hy, hx⟩ := mem_biUnion.mp hC
      obtain ⟨x, _, rfl⟩ := mem_image.mp hx
      have hy' := (mem_mggNearAxisCoord_iff y).mp hy
      simp [mggDecode_encode]
      rcases hy' with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))

theorem mggNearAxisRows_card_le {m : ℕ} (hm : 0 < m) :
    (mggNearAxisRows hm).card ≤ 3 * m := by
  classical
  letI : NeZero m := mggNeZero hm
  have hstrip : ∀ x : Fin m,
      ((univ : Finset (Fin m)).image fun y => mggEncode hm (x, y)).card ≤ m := by
    intro x
    refine (card_image_le).trans ?_
    simp [card_univ]
  calc
    (mggNearAxisRows hm).card
        ≤ ∑ x ∈ mggNearAxisCoord m,
            ((univ : Finset (Fin m)).image fun y => mggEncode hm (x, y)).card :=
      card_biUnion_le
    _ ≤ ∑ x ∈ mggNearAxisCoord m, m :=
      sum_le_sum fun x _ => hstrip x
    _ = (mggNearAxisCoord m).card * m := by
      simp [sum_const]
    _ ≤ 3 * m := Nat.mul_le_mul_right m (mggNearAxisCoord_card_le m)

theorem mggNearAxisCols_card_le {m : ℕ} (hm : 0 < m) :
    (mggNearAxisCols hm).card ≤ 3 * m := by
  classical
  letI : NeZero m := mggNeZero hm
  have hstrip : ∀ y : Fin m,
      ((univ : Finset (Fin m)).image fun x => mggEncode hm (x, y)).card ≤ m := by
    intro y
    refine (card_image_le).trans ?_
    simp [card_univ]
  calc
    (mggNearAxisCols hm).card
        ≤ ∑ y ∈ mggNearAxisCoord m,
            ((univ : Finset (Fin m)).image fun x => mggEncode hm (x, y)).card :=
      card_biUnion_le
    _ ≤ ∑ y ∈ mggNearAxisCoord m, m :=
      sum_le_sum fun y _ => hstrip y
    _ = (mggNearAxisCoord m).card * m := by
      simp [sum_const]
    _ ≤ 3 * m := Nat.mul_le_mul_right m (mggNearAxisCoord_card_le m)

/-- Density: `|nearAxis| ≤ 6m` (feeds `mgg_inv4_absorb_axis_budget_of_large`). -/
theorem mggNearAxis_card_le {m : ℕ} (hm : 0 < m) :
    (mggNearAxis m hm).card ≤ 6 * m := by
  rw [mggNearAxis_eq_rows_union_cols hm]
  calc
    (mggNearAxisRows hm ∪ mggNearAxisCols hm).card
        ≤ (mggNearAxisRows hm).card + (mggNearAxisCols hm).card :=
      card_union_le _ _
    _ ≤ 3 * m + 3 * m :=
      Nat.add_le_add (mggNearAxisRows_card_le hm) (mggNearAxisCols_card_le hm)
    _ = 6 * m := by ring

/-! ## Cluster 35: off-band excess ≤ 2

Uniform off-axis excess ≤ 2 fails at encode`(1,1)` (near-axis). Off the
near-axis band, shear images miss all translations; remaining collisions are
only within `{S,S⁻¹}` and `{T,T⁻¹}`, so leaving excess is at most 2. -/

/-- Off near-axis means both torus coordinates avoid `{0, 1, m-1}`. -/
theorem not_mem_mggNearAxis_iff {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    v ∉ mggNearAxis m hm ↔
      letI : NeZero m := mggNeZero hm
      let p := mggDecode hm v
      1 < p.1.val ∧ p.1.val + 1 < m ∧ 1 < p.2.val ∧ p.2.val + 1 < m := by
  letI : NeZero m := mggNeZero hm
  constructor
  · intro hv
    have h := (mem_mggNearAxis_iff hm v).not.mp hv
    simp only [not_or] at h
    exact ⟨Nat.lt_of_not_ge h.1, Nat.lt_of_not_ge h.2.1,
      Nat.lt_of_not_ge h.2.2.1, Nat.lt_of_not_ge h.2.2.2⟩
  · intro ⟨hx1, hx2, hy1, hy2⟩ hv
    have h := (mem_mggNearAxis_iff hm v).mp hv
    rcases h with h | h | h | h
    · exact absurd h (not_le_of_gt hx1)
    · exact absurd h (not_le_of_gt hx2)
    · exact absurd h (not_le_of_gt hy1)
    · exact absurd h (not_le_of_gt hy2)

/-- `S` shear family and `T` shear family (at most one collision each). -/
def mggShearSGens : Finset (Fin 8) := {mggS, mggSinv}
def mggShearTGens : Finset (Fin 8) := {mggT, mggTinv}

theorem mggShearGens_eq_S_union_T :
    mggShearGens = mggShearSGens ∪ mggShearTGens := by
  decide

theorem mggShearSGens_disjoint_T :
    Disjoint mggShearSGens mggShearTGens := by
  decide

private theorem mgg_fin_ne_one_of {m : ℕ} [NeZero m] {x : Fin m}
    (hx : 1 < x.val) : x ≠ 1 := by
  intro h
  have hm1 : 1 < m := by omega
  have hval : x.val = 1 := by
    simpa [Fin.val_one, Nat.mod_eq_of_lt hm1] using congrArg Fin.val h
  omega

private theorem mgg_fin_ne_neg_one_of {m : ℕ} [NeZero m] {x : Fin m}
    (hx : x.val + 1 < m) : x ≠ (-1 : Fin m) := by
  intro h
  have hm1 : 1 < m := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  have : x.val = n := by
    simpa [Fin.coe_neg_one] using congrArg Fin.val h
  omega

private theorem mgg_fin_add_right_eq_add_one {m : ℕ} [NeZero m] {x y : Fin m}
    (h : x + y = y + 1) : x = 1 :=
  add_right_cancel (h.trans (add_comm y 1))

private theorem mgg_fin_add_right_eq_sub_one {m : ℕ} [NeZero m] {x y : Fin m}
    (h : x + y = y - 1) : x = (-1 : Fin m) := by
  have h' : x + y = (-1) + y :=
    (h.trans (sub_eq_add_neg y 1)).trans (add_comm y (-1))
  exact add_right_cancel h'

private theorem mgg_fin_add_left_eq_add_one {m : ℕ} [NeZero m] {x y : Fin m}
    (h : x + y = x + 1) : y = 1 :=
  add_left_cancel h

private theorem mgg_fin_add_left_eq_sub_one {m : ℕ} [NeZero m] {x y : Fin m}
    (h : x + y = x - 1) : y = (-1 : Fin m) := by
  have h' : x + y = x + (-1) := by rwa [sub_eq_add_neg] at h
  exact add_left_cancel h'

private theorem mgg_fin_sub_right_eq_add_one {m : ℕ} [NeZero m] {x y : Fin m}
    (h : y - x = y + 1) : x = (-1 : Fin m) := by
  have h' : y + -x = y + 1 := by simpa [sub_eq_add_neg] using h
  have : -x = 1 := add_left_cancel h'
  simpa using congrArg (fun z : Fin m => -z) this

private theorem mgg_fin_sub_right_eq_sub_one {m : ℕ} [NeZero m] {x y : Fin m}
    (h : y - x = y - 1) : x = 1 := by
  have h' : y + -x = y + -1 := by simpa [sub_eq_add_neg] using h
  have : -x = -1 := add_left_cancel h'
  simpa using congrArg (fun z : Fin m => -z) this

private theorem mgg_fin_eq_sub_self_imp_zero {m : ℕ} [NeZero m] {x y : Fin m}
    (h : x = x - y) : y = 0 := by
  have h' : x = x + -y := by simpa [sub_eq_add_neg] using h
  have : x + -y = x := h'.symm
  have : -y = 0 := add_eq_left.mp this
  exact neg_eq_zero.mp this

private theorem mgg_offBand {m : ℕ} (hm : 0 < m) {v : Fin (m * m)}
    (hv : v ∉ mggNearAxis m hm) :
    letI : NeZero m := mggNeZero hm
    let p := mggDecode hm v
    1 < p.1.val ∧ p.1.val + 1 < m ∧ 1 < p.2.val ∧ p.2.val + 1 < m :=
  (not_mem_mggNearAxis_iff hm v).mp hv

/-- Off band, `S` misses every translation neighbor. -/
theorem mggNeighbor_S_ne_translation_of_not_mem_nearAxis {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (hv : v ∉ mggNearAxis m hm) {t : Fin 8}
    (ht : t ∈ mggTranslationGens) :
    mggNeighbor hm v mggS ≠ mggNeighbor hm v t := by
  letI : NeZero m := mggNeZero hm
  have ⟨hx1, hx2, hy1, hy2⟩ := mgg_offBand hm hv
  have ht' := (mem_mggTranslationGens_iff t).mp ht
  intro heq
  rcases ht' with hR | hL | hU | hD
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_S_eq hm v) (mggNeighbor_right_eq hm v) heq
    exact Fin.add_one_ne_of_one_lt (by omega) (mggDecode hm v).1
      (Prod.ext_iff.mp hpq).1.symm
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_S_eq hm v) (mggNeighbor_left_eq hm v) heq
    exact Fin.sub_one_ne_of_one_lt (by omega) (mggDecode hm v).1
      (Prod.ext_iff.mp hpq).1.symm
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_S_eq hm v) (mggNeighbor_up_eq hm v) heq
    exact mgg_fin_ne_one_of hx1
      (mgg_fin_add_right_eq_add_one (Prod.ext_iff.mp hpq).2)
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_S_eq hm v) (mggNeighbor_down_eq hm v) heq
    exact mgg_fin_ne_neg_one_of hx2
      (mgg_fin_add_right_eq_sub_one (Prod.ext_iff.mp hpq).2)

/-- Off band, `S⁻¹` misses every translation neighbor. -/
theorem mggNeighbor_Sinv_ne_translation_of_not_mem_nearAxis {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (hv : v ∉ mggNearAxis m hm) {t : Fin 8}
    (ht : t ∈ mggTranslationGens) :
    mggNeighbor hm v mggSinv ≠ mggNeighbor hm v t := by
  letI : NeZero m := mggNeZero hm
  have ⟨hx1, hx2, hy1, hy2⟩ := mgg_offBand hm hv
  have ht' := (mem_mggTranslationGens_iff t).mp ht
  intro heq
  rcases ht' with hR | hL | hU | hD
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Sinv_eq hm v) (mggNeighbor_right_eq hm v) heq
    exact Fin.add_one_ne_of_one_lt (by omega) (mggDecode hm v).1
      (Prod.ext_iff.mp hpq).1.symm
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Sinv_eq hm v) (mggNeighbor_left_eq hm v) heq
    exact Fin.sub_one_ne_of_one_lt (by omega) (mggDecode hm v).1
      (Prod.ext_iff.mp hpq).1.symm
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Sinv_eq hm v) (mggNeighbor_up_eq hm v) heq
    exact mgg_fin_ne_neg_one_of hx2
      (mgg_fin_sub_right_eq_add_one (Prod.ext_iff.mp hpq).2)
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Sinv_eq hm v) (mggNeighbor_down_eq hm v) heq
    exact mgg_fin_ne_one_of hx1
      (mgg_fin_sub_right_eq_sub_one (Prod.ext_iff.mp hpq).2)

/-- Off band, `T` misses every translation neighbor. -/
theorem mggNeighbor_T_ne_translation_of_not_mem_nearAxis {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (hv : v ∉ mggNearAxis m hm) {t : Fin 8}
    (ht : t ∈ mggTranslationGens) :
    mggNeighbor hm v mggT ≠ mggNeighbor hm v t := by
  letI : NeZero m := mggNeZero hm
  have ⟨hx1, hx2, hy1, hy2⟩ := mgg_offBand hm hv
  have ht' := (mem_mggTranslationGens_iff t).mp ht
  intro heq
  rcases ht' with hR | hL | hU | hD
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_T_eq hm v) (mggNeighbor_right_eq hm v) heq
    exact mgg_fin_ne_one_of hy1
      (mgg_fin_add_left_eq_add_one (Prod.ext_iff.mp hpq).1)
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_T_eq hm v) (mggNeighbor_left_eq hm v) heq
    exact mgg_fin_ne_neg_one_of hy2
      (mgg_fin_add_left_eq_sub_one (Prod.ext_iff.mp hpq).1)
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_T_eq hm v) (mggNeighbor_up_eq hm v) heq
    exact Fin.add_one_ne_of_one_lt (by omega) (mggDecode hm v).2
      (Prod.ext_iff.mp hpq).2.symm
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_T_eq hm v) (mggNeighbor_down_eq hm v) heq
    exact Fin.sub_one_ne_of_one_lt (by omega) (mggDecode hm v).2
      (Prod.ext_iff.mp hpq).2.symm

/-- Off band, `T⁻¹` misses every translation neighbor. -/
theorem mggNeighbor_Tinv_ne_translation_of_not_mem_nearAxis {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (hv : v ∉ mggNearAxis m hm) {t : Fin 8}
    (ht : t ∈ mggTranslationGens) :
    mggNeighbor hm v mggTinv ≠ mggNeighbor hm v t := by
  letI : NeZero m := mggNeZero hm
  have ⟨hx1, hx2, hy1, hy2⟩ := mgg_offBand hm hv
  have ht' := (mem_mggTranslationGens_iff t).mp ht
  intro heq
  rcases ht' with hR | hL | hU | hD
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Tinv_eq hm v) (mggNeighbor_right_eq hm v) heq
    have h1 := (Prod.ext_iff.mp hpq).1
    have h1' : (mggDecode hm v).1 + -((mggDecode hm v).2) =
        (mggDecode hm v).1 + 1 := by
      simpa [sub_eq_add_neg] using h1
    have : -((mggDecode hm v).2) = 1 := add_left_cancel h1'
    have hy : (mggDecode hm v).2 = (-1 : Fin m) := by
      simpa using congrArg (fun z : Fin m => -z) this
    exact mgg_fin_ne_neg_one_of hy2 hy
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Tinv_eq hm v) (mggNeighbor_left_eq hm v) heq
    have h1 := (Prod.ext_iff.mp hpq).1
    have h1' : (mggDecode hm v).1 + -((mggDecode hm v).2) =
        (mggDecode hm v).1 + -1 := by
      simpa [sub_eq_add_neg] using h1
    have : -((mggDecode hm v).2) = -1 := add_left_cancel h1'
    have hy : (mggDecode hm v).2 = 1 := by
      simpa using congrArg (fun z : Fin m => -z) this
    exact mgg_fin_ne_one_of hy1 hy
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Tinv_eq hm v) (mggNeighbor_up_eq hm v) heq
    exact Fin.add_one_ne_of_one_lt (by omega) (mggDecode hm v).2
      (Prod.ext_iff.mp hpq).2.symm
  · subst t
    have hpq := mgg_decode_neighbor_eq hm v
      (mggNeighbor_Tinv_eq hm v) (mggNeighbor_down_eq hm v) heq
    exact Fin.sub_one_ne_of_one_lt (by omega) (mggDecode hm v).2
      (Prod.ext_iff.mp hpq).2.symm

/-- Off band, every shear neighbor misses every translation neighbor. -/
theorem mggNeighbor_shear_ne_translation_of_not_mem_nearAxis {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (hv : v ∉ mggNearAxis m hm) {s t : Fin 8}
    (hs : s ∈ mggShearGens) (ht : t ∈ mggTranslationGens) :
    mggNeighbor hm v s ≠ mggNeighbor hm v t := by
  have hs' : s = mggS ∨ s = mggSinv ∨ s = mggT ∨ s = mggTinv := by
    simpa [mggShearGens, mem_insert, mem_singleton] using hs
  rcases hs' with hs | hs | hs | hs <;> subst s
  · exact mggNeighbor_S_ne_translation_of_not_mem_nearAxis hm v hv ht
  · exact mggNeighbor_Sinv_ne_translation_of_not_mem_nearAxis hm v hv ht
  · exact mggNeighbor_T_ne_translation_of_not_mem_nearAxis hm v hv ht
  · exact mggNeighbor_Tinv_ne_translation_of_not_mem_nearAxis hm v hv ht

/-- Off band, `S`-family images miss `T`-family images. -/
theorem mggNeighbor_S_family_ne_T_family_of_not_mem_nearAxis {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (hv : v ∉ mggNearAxis m hm) {s t : Fin 8}
    (hs : s ∈ mggShearSGens) (ht : t ∈ mggShearTGens) :
    mggNeighbor hm v s ≠ mggNeighbor hm v t := by
  letI : NeZero m := mggNeZero hm
  have ⟨hx1, hx2, hy1, hy2⟩ := mgg_offBand hm hv
  have hs' : s = mggS ∨ s = mggSinv := by
    simpa [mggShearSGens, mem_insert, mem_singleton] using hs
  have ht' : t = mggT ∨ t = mggTinv := by
    simpa [mggShearTGens, mem_insert, mem_singleton] using ht
  intro heq
  have hy0 : (mggDecode hm v).2 = 0 := by
    rcases hs' with hs | hs <;> rcases ht' with ht | ht <;> subst s <;> subst t
    · have hpq := mgg_decode_neighbor_eq hm v
        (mggNeighbor_S_eq hm v) (mggNeighbor_T_eq hm v) heq
      exact add_eq_left.mp (Prod.ext_iff.mp hpq).1.symm
    · have hpq := mgg_decode_neighbor_eq hm v
        (mggNeighbor_S_eq hm v) (mggNeighbor_Tinv_eq hm v) heq
      exact mgg_fin_eq_sub_self_imp_zero (Prod.ext_iff.mp hpq).1
    · have hpq := mgg_decode_neighbor_eq hm v
        (mggNeighbor_Sinv_eq hm v) (mggNeighbor_T_eq hm v) heq
      exact add_eq_left.mp (Prod.ext_iff.mp hpq).1.symm
    · have hpq := mgg_decode_neighbor_eq hm v
        (mggNeighbor_Sinv_eq hm v) (mggNeighbor_Tinv_eq hm v) heq
      exact mgg_fin_eq_sub_self_imp_zero (Prod.ext_iff.mp hpq).1
  have : (mggDecode hm v).2.val = 0 := congrArg Fin.val hy0
  omega

private theorem mgg_card_sub_image_le_one {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (hc : s.card ≤ 2) :
    s.card - (s.image f).card ≤ 1 := by
  classical
  have hi := card_image_le (f := f) (s := s)
  by_cases hne : s.Nonempty
  · have himg : 0 < (s.image f).card := card_pos.mpr (hne.image _)
    omega
  · have : s.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hne)
    omega

/-- Off band, leaving excess is at most 2 (Inv absorb `2o` term). -/
theorem mggLeavingExcess_le_two_of_not_mem_nearAxis {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m))
    (hv : v ∉ mggNearAxis m (lt_of_lt_of_le (by decide : 0 < 3) hm)) :
    mggLeavingExcess (lt_of_lt_of_le (by decide : 0 < 3) hm) S v ≤ 2 := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  set L := mggLeavingGens hm0 S v with hLdef
  set T := mggTranslationGens ∩ L with hTdef
  set Sh := mggShearGens ∩ L with hShdef
  set ShS := mggShearSGens ∩ L with hShSdef
  set ShT := mggShearTGens ∩ L with hShTdef
  have hSh : Sh = L \ mggTranslationGens := by
    ext s
    constructor
    · intro hs
      refine mem_sdiff.mpr ⟨(mem_inter.mp hs).2, ?_⟩
      intro hT
      have hdisj : Disjoint mggShearGens mggTranslationGens := by decide
      exact Finset.disjoint_left.1 hdisj (mem_inter.mp hs).1 hT
    · intro hs
      have hUT : (univ : Finset (Fin 8)) \ mggTranslationGens = mggShearGens := by
        decide
      refine mem_inter.mpr ⟨?_, (mem_sdiff.mp hs).1⟩
      have : s ∈ (univ : Finset (Fin 8)) \ mggTranslationGens :=
        mem_sdiff.mpr ⟨mem_univ s, (mem_sdiff.mp hs).2⟩
      simpa [hUT] using this
  have hLsplit : L.card = T.card + Sh.card := by
    have : L.card = T.card + (L \ mggTranslationGens).card := by
      rw [← card_inter_add_card_sdiff L mggTranslationGens, inter_comm]
    simpa [hSh] using this
  have hSh' : Sh = ShS ∪ ShT := by
    calc
      Sh = mggShearGens ∩ L := rfl
      _ = (mggShearSGens ∪ mggShearTGens) ∩ L := by rw [mggShearGens_eq_S_union_T]
      _ = (mggShearSGens ∩ L) ∪ (mggShearTGens ∩ L) := by
          rw [union_inter_distrib_right]
      _ = ShS ∪ ShT := rfl
  have hdisjST : Disjoint ShS ShT :=
    Disjoint.mono inter_subset_left inter_subset_left mggShearSGens_disjoint_T
  have hShsplit : Sh.card = ShS.card + ShT.card := by
    rw [hSh', card_union_of_disjoint hdisjST]
  have hShex : Sh.card - (Sh.image (mggNeighbor hm0 v)).card ≤ 2 := by
    have hunion : Sh.image (mggNeighbor hm0 v) =
        ShS.image (mggNeighbor hm0 v) ∪ ShT.image (mggNeighbor hm0 v) := by
      rw [hSh', image_union]
    have hdisj :
        Disjoint (ShS.image (mggNeighbor hm0 v))
          (ShT.image (mggNeighbor hm0 v)) := by
      refine disjoint_left.2 ?_
      intro w hwS hwT
      obtain ⟨s, hsS, rfl⟩ := mem_image.mp hwS
      obtain ⟨t, htT, hwt⟩ := mem_image.mp hwT
      exact mggNeighbor_S_family_ne_T_family_of_not_mem_nearAxis hm0 v hv
        (mem_inter.mp hsS).1 (mem_inter.mp htT).1 hwt.symm
    have hSimg :
        (Sh.image (mggNeighbor hm0 v)).card =
          (ShS.image (mggNeighbor hm0 v)).card +
            (ShT.image (mggNeighbor hm0 v)).card := by
      rw [hunion, card_union_of_disjoint hdisj]
    have hSle :=
      mgg_card_sub_image_le_one ShS (mggNeighbor hm0 v)
        ((card_le_card inter_subset_left).trans
          (by decide : mggShearSGens.card ≤ 2))
    have hTle' :=
      mgg_card_sub_image_le_one ShT (mggNeighbor hm0 v)
        ((card_le_card inter_subset_left).trans
          (by decide : mggShearTGens.card ≤ 2))
    omega
  have hdisjTS :
      Disjoint (T.image (mggNeighbor hm0 v)) (Sh.image (mggNeighbor hm0 v)) := by
    refine disjoint_left.2 ?_
    intro w hwT hwSh
    obtain ⟨t, htT, rfl⟩ := mem_image.mp hwT
    obtain ⟨s, hsSh, hws⟩ := mem_image.mp hwSh
    exact mggNeighbor_shear_ne_translation_of_not_mem_nearAxis hm0 v hv
      (mem_inter.mp hsSh).1 (mem_inter.mp htT).1 hws
  have himgL :
      T.card + (Sh.image (mggNeighbor hm0 v)).card ≤
        (mggOutNeighbors hm0 S v).card := by
    have hsub :
        T.image (mggNeighbor hm0 v) ∪ Sh.image (mggNeighbor hm0 v) ⊆
          mggOutNeighbors hm0 S v := by
      intro w hw
      rcases mem_union.mp hw with hw | hw
      · obtain ⟨s, hsT, rfl⟩ := mem_image.mp hw
        exact mem_image.mpr ⟨s, (mem_inter.mp hsT).2, rfl⟩
      · obtain ⟨s, hsSh, rfl⟩ := mem_image.mp hw
        exact mem_image.mpr ⟨s, (mem_inter.mp hsSh).2, rfl⟩
    have hcard :
        (T.image (mggNeighbor hm0 v) ∪ Sh.image (mggNeighbor hm0 v)).card =
          (T.image (mggNeighbor hm0 v)).card +
            (Sh.image (mggNeighbor hm0 v)).card :=
      card_union_of_disjoint hdisjTS
    have hinj : Set.InjOn (mggNeighbor hm0 v) (T : Set (Fin 8)) :=
      (mggNeighbor_translation_injOn hm v).mono fun s hs => (mem_inter.mp hs).1
    have hTcard : (T.image (mggNeighbor hm0 v)).card = T.card :=
      card_image_of_injOn hinj
    have := card_le_card hsub
    omega
  have : L.card - (mggOutNeighbors hm0 S v).card ≤ 2 := by
    have h1 : L.card - (mggOutNeighbors hm0 S v).card ≤
        L.card - (T.card + (Sh.image (mggNeighbor hm0 v)).card) :=
      Nat.sub_le_sub_left himgL _
    have h2 : L.card - (T.card + (Sh.image (mggNeighbor hm0 v)).card) =
        Sh.card - (Sh.image (mggNeighbor hm0 v)).card := by
      omega
    calc
      L.card - (mggOutNeighbors hm0 S v).card
          ≤ L.card - (T.card + (Sh.image (mggNeighbor hm0 v)).card) := h1
      _ = Sh.card - (Sh.image (mggNeighbor hm0 v)).card := h2
      _ ≤ 2 := hShex
  simpa [mggLeavingExcess, L] using this

/-- Reverse loss ≤ `4|S ∩ nearAxis| + 2|S \ nearAxis|`. -/
theorem mggReverseCutLoss_le_four_near_two_off {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggReverseCutLoss (lt_of_lt_of_le (by decide : 0 < 3) hm) S ≤
      4 * (S ∩ mggNearAxis m (lt_of_lt_of_le (by decide : 0 < 3) hm)).card +
        2 * (S \ mggNearAxis m (lt_of_lt_of_le (by decide : 0 < 3) hm)).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  let near := mggNearAxis m hm0
  have hterm :
      (∑ v ∈ S, mggLeavingExcess hm0 S v) ≤
        ∑ v ∈ S, (if v ∈ near then (4 : ℕ) else 2) := by
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ near
    · simpa [hv] using mggLeavingExcess_le_four hm S v
    · simpa [hv] using mggLeavingExcess_le_two_of_not_mem_nearAxis hm S v hv
  have hsplit :
      (∑ v ∈ S, (if v ∈ near then (4 : ℕ) else 2)) =
        4 * (S ∩ near).card + 2 * (S \ near).card := by
    have hite :=
      (Finset.sum_ite (s := S) (p := fun v => v ∈ near)
        (f := fun _ => (4 : ℕ)) (g := fun _ => (2 : ℕ)))
    have hfilter : S.filter (fun v => v ∉ near) = S \ near := by
      ext x; simp [mem_filter, mem_sdiff]
    have hnearF : S.filter (fun v => v ∈ near) = S ∩ near := filter_mem_eq_inter
    calc
      (∑ v ∈ S, (if v ∈ near then (4 : ℕ) else 2))
          = (∑ v ∈ S.filter (fun v => v ∈ near), 4) +
              ∑ v ∈ S.filter (fun v => v ∉ near), 2 := hite
      _ = (∑ v ∈ S ∩ near, 4) + ∑ v ∈ S \ near, 2 := by
            simp [hnearF, hfilter]
      _ = 4 * (S ∩ near).card + 2 * (S \ near).card := by
            simp [sum_const, nsmul_eq_mul, Nat.mul_comm]
  exact (by simpa [mggReverseCutLoss, near] using hterm.trans (le_of_eq hsplit))

/-! ## Cluster 36: Inv-4 absorb packaging from near loss

Cluster 35 gave `reverseLoss ≤ 4a + 2o`. This cluster packages Inv-4 on a set
from multi Cheeger plus a twelfth reverseLoss budget, and records the
`|S ∩ nearAxis| ≤ 6m` and `reverseLoss ≤ 2|S| + 12m` corollaries. Spectral
Cheeger on the multi cut remains Frontier. -/

/-- Intersection with the near-axis band is at most `6m`. -/
theorem card_inter_mggNearAxis_le {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (S ∩ mggNearAxis m hm).card ≤ 6 * m :=
  (card_le_card (Finset.inter_subset_right)).trans (mggNearAxis_card_le hm)

/-- Coarse form: `reverseLoss ≤ 2|S| + 12m` via `4a + 2o = 2|S| + 2a`. -/
theorem mggReverseCutLoss_le_two_mul_card_add_twelve_mul_m {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggReverseCutLoss (lt_of_lt_of_le (by decide : 0 < 3) hm) S ≤
      2 * S.card + 12 * m := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  let near := mggNearAxis m hm0
  have h := mggReverseCutLoss_le_four_near_two_off hm S
  have ha : (S ∩ near).card ≤ 6 * m := card_inter_mggNearAxis_le hm0 S
  have hsplit : 4 * (S ∩ near).card + 2 * (S \ near).card =
      2 * S.card + 2 * (S ∩ near).card := by
    have ho : (S ∩ near).card + (S \ near).card = S.card := by
      rw [← card_inter_add_card_sdiff S near]
    omega
  have h2 : 2 * S.card + 2 * (S ∩ near).card ≤ 2 * S.card + 12 * m := by
    have : 2 * (S ∩ near).card ≤ 12 * m := by
      have := Nat.mul_le_mul_left 2 ha
      omega
    omega
  calc
    mggReverseCutLoss hm0 S
        ≤ 4 * (S ∩ near).card + 2 * (S \ near).card := h
    _ = 2 * S.card + 2 * (S ∩ near).card := hsplit
    _ ≤ 2 * S.card + 12 * m := h2

/-- From multi Cheeger and twelfth reverseLoss, conclude Inv-4 on one set. -/
theorem mgg_card_le_four_mul_edgeBoundary_of_multi_and_twelfth {m : ℕ}
    (hm : 0 < m) (S : Finset (Fin (m * m)))
    (hcheeger : S.card ≤ 3 * mggMultiCutCard hm S)
    (htwelfth : 12 * mggReverseCutLoss hm S ≤ S.card) :
    S.card ≤ 4 * (edgeBoundary (mggGraph m hm) S).card := by
  have hle := mggMultiCutCard_le_edgeBoundary_add_reverseLoss hm S
  have hmain : S.card ≤
      3 * ((edgeBoundary (mggGraph m hm) S).card + mggReverseCutLoss hm S) :=
    hcheeger.trans (Nat.mul_le_mul_left 3 hle)
  exact mgg_inv4_absorb_of_loss_le_twelfth hmain htwelfth

/-- Same Inv-4 glue using the `4a + 2o` reverseLoss bound as the twelfth witness. -/
theorem mgg_card_le_four_mul_edgeBoundary_of_multi_near_two_off {m : ℕ}
    (hm : 3 ≤ m) (S : Finset (Fin (m * m)))
    (hcheeger :
      S.card ≤ 3 * mggMultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S)
    (htwelfth :
      12 *
          (4 *
              (S ∩
                  mggNearAxis m
                    (lt_of_lt_of_le (by decide : 0 < 3) hm)).card +
            2 *
              (S \
                  mggNearAxis m
                    (lt_of_lt_of_le (by decide : 0 < 3) hm)).card) ≤
        S.card) :
    S.card ≤
      4 *
        (edgeBoundary (mggGraph m (lt_of_lt_of_le (by decide : 0 < 3) hm))
            S).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have hloss := mggReverseCutLoss_le_four_near_two_off hm S
  have htwelfth' : 12 * mggReverseCutLoss hm0 S ≤ S.card :=
    (Nat.mul_le_mul_left 12 hloss).trans htwelfth
  exact mgg_card_le_four_mul_edgeBoundary_of_multi_and_twelfth hm0 S hcheeger
    htwelfth'

/-- Nat form: `4a + 2o` twelfth budget with `a ≤ 6m` reduces to a size check. -/
theorem mgg_inv4_absorb_near_two_off_of_large {s g a o m : ℕ}
    (hmain : s ≤ 3 * (g + (4 * a + 2 * o)))
    (_ha : a ≤ 6 * m)
    (hb : 48 * a + 24 * o ≤ s) : s ≤ 4 * g := by
  have hloss : 12 * (4 * a + 2 * o) ≤ s := by
    simpa [show 12 * (4 * a + 2 * o) = 48 * a + 24 * o from by ring] using hb
  exact mgg_inv4_absorb_of_near_loss hmain hloss

/-! ## Cluster 37: multi Cheeger Nat surface and Inv packaging

Cluster 36 left spectral multi Cheeger open. This cluster pins the Nat
Cheeger inequality from Gabber Galil constants, names the multi cut
hypothesis, packages it to `HasExpansionInv` under a twelfth reverseLoss
witness, and records that the coarse `2|S|+12m` loss bound cannot supply
that twelfth. -/

/-- Nat form of `(8 − 5√2)/2 ≥ 2/5`: equivalent to `36² > 2 · 25²`. -/
theorem mgg_cheeger_two_fifth_nat : 36 * 36 > 2 * (25 * 25) := by
  decide

/-- From `5√2 < 71/10` (Cluster 30 witness) and `36² > 2·25²`, recover
`(8 − 5√2)/2 ≥ 2/5` as a rational comparison proxy used by packaging. -/
theorem mgg_cheeger_gap_rational_proxy :
    (8 * 10 - 71) * 5 ≥ 4 * 10 := by
  decide

/-- Multi cut Cheeger at rate `2/5`: every nonempty half set expands. -/
def MggHasMultiCheeger (m : ℕ) (hm : 0 < m) : Prop :=
  ∀ S : Finset (Fin (m * m)),
    S.Nonempty → 2 * S.card ≤ m * m →
      2 * S.card ≤ 5 * mggMultiCutCard hm S

/-- Multi Cheeger implies the Inv-3 form used by absorb (`|S| ≤ 3|∂_M|`). -/
theorem mgg_card_le_three_mul_multiCut_of_cheeger {m : ℕ} (hm : 0 < m)
    (h : MggHasMultiCheeger m hm) (S : Finset (Fin (m * m)))
    (hne : S.Nonempty) (hhalf : 2 * S.card ≤ m * m) :
    S.card ≤ 3 * mggMultiCutCard hm S :=
  mgg_card_le_three_mul_of_two_fifth (h S hne hhalf)

/-- Coarse reverseLoss `≤ 2|S| + 12m` never meets the twelfth budget when `|S| > 0`. -/
theorem not_twelfth_of_two_mul_card_add_twelve_mul_m {s m : ℕ}
    (hs : 0 < s) : ¬ (12 * (2 * s + 12 * m) ≤ s) := by
  intro h
  omega

/-- From multi Cheeger plus a pointwise twelfth reverseLoss witness, conclude
`HasExpansionInv` at `mggInvK`. Spectral discharge of `MggHasMultiCheeger`
remains Frontier. -/
theorem mggGraph_hasExpansionInv_of_multi_cheeger_and_twelfth {m : ℕ}
    (hm : 0 < m) (hcheeger : MggHasMultiCheeger m hm)
    (htwelfth : ∀ S : Finset (Fin (m * m)),
      S.Nonempty → 2 * S.card ≤ m * m →
        12 * mggReverseCutLoss hm S ≤ S.card) :
    HasExpansionInv (mggGraph m hm) mggInvK := by
  intro S hne hhalf
  have h3 := mgg_card_le_three_mul_multiCut_of_cheeger hm hcheeger S hne hhalf
  exact mgg_card_le_four_mul_edgeBoundary_of_multi_and_twelfth hm S h3
    (htwelfth S hne hhalf)

/-! ## Cluster 38: reverseLoss vs edgeBoundary and Inv-15 packaging

Cluster 37 showed coarse `2|S|+12m` cannot twelfth-absorb. Spectral multi
Cheeger remains open. This cluster proves leaving excess is at most four times
the out-neighbor count, hence `reverseLoss ≤ 4|∂_G|`, and packages Inv-15 from
`MggHasMultiCheeger` alone (no twelfth). Inv-4 still needs spectral plus a
sharper loss or twelfth witness. -/

/-- If there are no outside neighbors then leaving excess is zero. -/
theorem mggLeavingExcess_eq_zero_of_outNeighbors_empty {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m))
    (h : (mggOutNeighbors hm S v).card = 0) :
    mggLeavingExcess hm S v = 0 := by
  have hempty : mggOutNeighbors hm S v = ∅ := card_eq_zero.mp h
  have hL : mggLeavingGens hm S v = ∅ := by
    simpa [mggOutNeighbors] using (Finset.image_eq_empty.mp hempty)
  simp [mggLeavingExcess, hL]

/-- Excess ≤ `4 · |outNeighbors|` (uses global excess ≤ 4 for `m ≥ 3`). -/
theorem mggLeavingExcess_le_four_mul_outNeighbors {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    mggLeavingExcess (lt_of_lt_of_le (by decide : 0 < 3) hm) S v ≤
      4 * (mggOutNeighbors (lt_of_lt_of_le (by decide : 0 < 3) hm) S v).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  by_cases h0 : (mggOutNeighbors hm0 S v).card = 0
  · rw [mggLeavingExcess_eq_zero_of_outNeighbors_empty hm0 S v h0]
    exact Nat.zero_le _
  · have hpos : 0 < (mggOutNeighbors hm0 S v).card := Nat.pos_of_ne_zero h0
    have hex := mggLeavingExcess_le_four hm S v
    have : 4 ≤ 4 * (mggOutNeighbors hm0 S v).card := by omega
    exact hex.trans this

/-- Reverse loss ≤ `4|∂_G S|`. -/
theorem mggReverseCutLoss_le_four_mul_edgeBoundary {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggReverseCutLoss (lt_of_lt_of_le (by decide : 0 < 3) hm) S ≤
      4 * (edgeBoundary (mggGraph m (lt_of_lt_of_le (by decide : 0 < 3) hm))
          S).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have hterm :
      (∑ v ∈ S, mggLeavingExcess hm0 S v) ≤
        ∑ v ∈ S, 4 * (mggOutNeighbors hm0 S v).card :=
    Finset.sum_le_sum fun v _ => mggLeavingExcess_le_four_mul_outNeighbors hm S v
  have hmul :
      (∑ v ∈ S, 4 * (mggOutNeighbors hm0 S v).card) =
        4 * ∑ v ∈ S, (mggOutNeighbors hm0 S v).card := by
    simp [Finset.mul_sum]
  have hsum : mggReverseCutLoss hm0 S ≤
      4 * ∑ v ∈ S, (mggOutNeighbors hm0 S v).card := by
    simpa [mggReverseCutLoss, hmul] using hterm
  have hle := sum_mggOutNeighbors_card_le_edgeBoundary hm0 S
  exact hsum.trans (Nat.mul_le_mul_left 4 hle)

/-- From multi Cheeger alone, Inv-15 on the simple graph (`reverseLoss ≤ 4|∂_G|`). -/
theorem mgg_card_le_fifteen_mul_edgeBoundary_of_multi_cheeger {m : ℕ}
    (hm : 3 ≤ m) (hcheeger : MggHasMultiCheeger m
      (lt_of_lt_of_le (by decide : 0 < 3) hm))
    (S : Finset (Fin (m * m))) (hne : S.Nonempty)
    (hhalf : 2 * S.card ≤ m * m) :
    S.card ≤
      15 *
        (edgeBoundary (mggGraph m (lt_of_lt_of_le (by decide : 0 < 3) hm))
            S).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have h3 := mgg_card_le_three_mul_multiCut_of_cheeger hm0 hcheeger S hne hhalf
  have hmulti := mggMultiCutCard_le_edgeBoundary_add_reverseLoss hm0 S
  have hloss := mggReverseCutLoss_le_four_mul_edgeBoundary hm S
  set g := (edgeBoundary (mggGraph m hm0) S).card
  have hmain : S.card ≤ 3 * (g + 4 * g) := by
    have : mggMultiCutCard hm0 S ≤ g + 4 * g :=
      hmulti.trans (Nat.add_le_add_left hloss g)
    have : mggMultiCutCard hm0 S ≤ 5 * g := by omega
    have : S.card ≤ 3 * (5 * g) := h3.trans (Nat.mul_le_mul_left 3 this)
    omega
  have : 3 * (g + 4 * g) = 15 * g := by ring
  simpa [this] using hmain

namespace MGGFrontier

/-- Gabber Galil spectral input: labeled 8-regular multi Cayley graph has
multi Cheeger rate `2/5` (external; analysis not formalized). -/
theorem mgg_has_multi_cheeger_of_gabber_galil (m : ℕ) (hm0 : 0 < m)
    (_hm : mggInformativeFloor ≤ m) :
    MggHasMultiCheeger m hm0 := by
  sorry

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
