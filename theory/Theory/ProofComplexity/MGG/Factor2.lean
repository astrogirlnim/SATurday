import Theory.ProofComplexity.MGG
import Mathlib.Tactic

/-!
# Factor-2 Margulis–Gabber–Galil simple graph (R2 Block A checklist item 1)

Eight labeled Jimbo–Maruoka / AFP steps on the same `(Z/mZ)²` vertex set as
unit-shear `mggNeighbor`:
`(x ± 2y, y)`, `(x ± (2y+1), y)`, `(x, y ± 2x)`, `(x, y ± (2x+1))`.
Matches `MGGFrontier.mggImport_mgg_graph_step` with labels `(l, σ)`, `σ ∈ {±1}`.

Reuses accepted `mggDecode`, `mggEncode`, `mggEncode_decode`, `mggDecode_encode`.
Does not touch the certified unit-shear surface (`mggNeighbor`, `mggGraph`, …).

Connectivity: `(2y+1) - 2y = 1` gives unit horizontal walks; likewise vertical.
The factor-2 Rayleigh form and multi-Cheeger packaging live in `MGG.Factor2Spectral`.
LOG: R2 Block A factor-2 FinGraph multi-cut connectivity
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

private theorem mggF2NeZero {m : ℕ} (hm : 0 < m) : NeZero m := ⟨ne_of_gt hm⟩

/-! ## Labeled factor-2 generators (Fin 8) -/

/-- `(x + 2y, y)`; AFP `l = 0`, `σ = +1`. -/
def mggF2Xp2y : Fin 8 := ⟨0, by decide⟩
/-- `(x - 2y, y)`; AFP `l = 0`, `σ = -1`. -/
def mggF2Xm2y : Fin 8 := ⟨1, by decide⟩
/-- `(x, y + 2x)`; AFP `l = 1`, `σ = +1`. -/
def mggF2Yp2x : Fin 8 := ⟨2, by decide⟩
/-- `(x, y - 2x)`; AFP `l = 1`, `σ = -1`. -/
def mggF2Ym2x : Fin 8 := ⟨3, by decide⟩
/-- `(x + 2y + 1, y)`; AFP `l = 2`, `σ = +1`. -/
def mggF2Xp2y1 : Fin 8 := ⟨4, by decide⟩
/-- `(x - (2y + 1), y)`; AFP `l = 2`, `σ = -1`. -/
def mggF2Xm2y1 : Fin 8 := ⟨5, by decide⟩
/-- `(x, y + 2x + 1)`; AFP `l = 3`, `σ = +1`. -/
def mggF2Yp2x1 : Fin 8 := ⟨6, by decide⟩
/-- `(x, y - (2x + 1))`; AFP `l = 3`, `σ = -1`. -/
def mggF2Ym2x1 : Fin 8 := ⟨7, by decide⟩

/-- Eight labeled factor-2 neighbors on `Fin (m * m)`. -/
def mggF2Neighbor {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    Fin (m * m) :=
  letI : NeZero m := mggF2NeZero hm
  let x := (mggDecode hm v).1
  let y := (mggDecode hm v).2
  if s.val = 0 then mggEncode hm (x + y + y, y)
  else if s.val = 1 then mggEncode hm (x - y - y, y)
  else if s.val = 2 then mggEncode hm (x, y + x + x)
  else if s.val = 3 then mggEncode hm (x, y - x - x)
  else if s.val = 4 then mggEncode hm (x + y + y + 1, y)
  else if s.val = 5 then mggEncode hm (x - y - y - 1, y)
  else if s.val = 6 then mggEncode hm (x, y + x + x + 1)
  else mggEncode hm (x, y - x - x - 1)

/-- Undirected simple edge between `v` and `mggF2Neighbor v s` when distinct. -/
def mggF2EdgeOf {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    Option (FinEdge (m * m)) :=
  let w := mggF2Neighbor hm v s
  if h : v.val < w.val then
    some ⟨(v, w), h⟩
  else if h : w.val < v.val then
    some ⟨(w, v), h⟩
  else
    none

/-- Factor-2 Margulis–Gabber–Galil simple graph on `m * m` vertices. -/
def mggF2Graph (m : ℕ) (hm : 0 < m) : FinGraph (m * m) :=
  (Finset.univ : Finset (Fin (m * m))).biUnion fun v =>
    (Finset.univ : Finset (Fin 8)).biUnion fun s =>
      match mggF2EdgeOf hm v s with
      | some e => {e}
      | none => ∅

theorem mem_mggF2Graph_of_edgeOf {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8)
    {e : FinEdge (m * m)} (he : mggF2EdgeOf hm v s = some e) :
    e ∈ mggF2Graph m hm := by
  refine mem_biUnion.mpr ⟨v, mem_univ v, ?_⟩
  refine mem_biUnion.mpr ⟨s, mem_univ s, ?_⟩
  simp [he]

/-- Labeled multi-cut size: factor-2 generator incidences leaving `S`. -/
def mggF2MultiCutCard {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) : ℕ :=
  ∑ v ∈ S, ((Finset.univ : Finset (Fin 8)).filter fun s =>
    mggF2Neighbor hm v s ∉ S).card

/-- Leaving generator labels at a vertex for the factor-2 star. -/
def mggF2LeavingGens {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : Finset (Fin 8) :=
  (Finset.univ : Finset (Fin 8)).filter fun s => mggF2Neighbor hm v s ∉ S

theorem mem_mggF2LeavingGens_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (s : Fin 8) :
    s ∈ mggF2LeavingGens hm S v ↔ mggF2Neighbor hm v s ∉ S := by
  simp [mggF2LeavingGens]

theorem mggF2LeavingGens_card_sum {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (∑ v ∈ S, (mggF2LeavingGens hm S v).card) = mggF2MultiCutCard hm S := by
  simp only [mggF2LeavingGens, mggF2MultiCutCard]

/-! ## Neighbor equations -/

theorem mggF2Neighbor_Xp2y1_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Xp2y1 =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1 + (mggDecode hm v).2 + (mggDecode hm v).2 + 1,
          (mggDecode hm v).2) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Xm2y_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Xm2y =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1 - (mggDecode hm v).2 - (mggDecode hm v).2,
          (mggDecode hm v).2) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Yp2x1_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Yp2x1 =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1,
          (mggDecode hm v).2 + (mggDecode hm v).1 + (mggDecode hm v).1 + 1) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Ym2x_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Ym2x =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1,
          (mggDecode hm v).2 - (mggDecode hm v).1 - (mggDecode hm v).1) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Xp2y_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Xp2y =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1 + (mggDecode hm v).2 + (mggDecode hm v).2,
          (mggDecode hm v).2) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Yp2x_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Yp2x =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1,
          (mggDecode hm v).2 + (mggDecode hm v).1 + (mggDecode hm v).1) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Xm2y1_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Xm2y1 =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1 - (mggDecode hm v).2 - (mggDecode hm v).2 - 1,
          (mggDecode hm v).2) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2Neighbor_Ym2x1_eq {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Ym2x1 =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm
        ((mggDecode hm v).1,
          (mggDecode hm v).2 - (mggDecode hm v).1 - (mggDecode hm v).1 - 1) := by
  letI : NeZero m := mggF2NeZero hm
  rfl

theorem mggF2EdgeOf_eq_some_of_ne {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8)
    (hne : mggF2Neighbor hm v s ≠ v) :
    ∃ e, mggF2EdgeOf hm v s = some e ∧
      ((e.val.1 = v ∧ e.val.2 = mggF2Neighbor hm v s) ∨
        (e.val.1 = mggF2Neighbor hm v s ∧ e.val.2 = v)) := by
  dsimp [mggF2EdgeOf]
  set w := mggF2Neighbor hm v s
  by_cases hlt : v.val < w.val
  · refine ⟨⟨(v, w), hlt⟩, ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp [hlt]
  · have hwv : w.val < v.val := by
      have : w.val ≠ v.val := fun heq => hne (Fin.ext heq)
      omega
    refine ⟨⟨(w, v), hwv⟩, ?_, Or.inr ⟨rfl, rfl⟩⟩
    simp [hlt, hwv]

theorem mggF2_adj_of_neighbor_ne {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8)
    (hne : mggF2Neighbor hm v s ≠ v) :
    (mggF2Graph m hm).Adj v (mggF2Neighbor hm v s) := by
  obtain ⟨e, he, hends⟩ := mggF2EdgeOf_eq_some_of_ne hm v s hne
  refine ⟨e, mem_mggF2Graph_of_edgeOf hm v s he, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ## Unit walks via shear composition `(2y+1) - 2y = 1` -/

private def mggF2FinMod {m : ℕ} (hm : 0 < m) (n : ℕ) : Fin m :=
  ⟨n % m, Nat.mod_lt n hm⟩

/-- Fin identity: `(x + y + y + 1) - y - y = x + 1`. -/
theorem mggF2_fin_x_succ_cancel {m : ℕ} [NeZero m] (x y : Fin m) :
    (x + y + y + 1) - y - y = x + 1 := by
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Fin identity: `(y + x + x + 1) - x - x = y + 1`. -/
theorem mggF2_fin_y_succ_cancel {m : ℕ} [NeZero m] (x y : Fin m) :
    (y + x + x + 1) - x - x = y + 1 :=
  mggF2_fin_x_succ_cancel y x

/-- After `+(2y+1)` then `-2y`, the encoded x-coordinate advances by one. -/
theorem mggF2_x_succ_via_shears {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2Neighbor hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1) mggF2Xm2y =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm (x + 1, y) := by
  letI : NeZero m := mggF2NeZero hm
  set v0 := mggEncode hm (x, y)
  have hdec0 : mggDecode hm v0 = (x, y) := mggDecode_encode hm (x, y)
  have hv1 :
      mggF2Neighbor hm v0 mggF2Xp2y1 = mggEncode hm (x + y + y + 1, y) := by
    simp [mggF2Neighbor_Xp2y1_eq, hdec0]
  set v1 := mggF2Neighbor hm v0 mggF2Xp2y1
  have hdec1 : mggDecode hm v1 = (x + y + y + 1, y) := by
    rw [hv1, mggDecode_encode]
  change mggF2Neighbor hm v1 mggF2Xm2y = mggEncode hm (x + 1, y)
  rw [mggF2Neighbor_Xm2y_eq, hdec1]
  congr 1
  exact Prod.ext (mggF2_fin_x_succ_cancel x y) rfl

/-- After `+(2x+1)` then `-2x`, the encoded y-coordinate advances by one. -/
theorem mggF2_y_succ_via_shears {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2Neighbor hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1) mggF2Ym2x =
      letI : NeZero m := mggF2NeZero hm
      mggEncode hm (x, y + 1) := by
  letI : NeZero m := mggF2NeZero hm
  set v0 := mggEncode hm (x, y)
  have hdec0 : mggDecode hm v0 = (x, y) := mggDecode_encode hm (x, y)
  have hv1 :
      mggF2Neighbor hm v0 mggF2Yp2x1 = mggEncode hm (x, y + x + x + 1) := by
    simp [mggF2Neighbor_Yp2x1_eq, hdec0]
  set v1 := mggF2Neighbor hm v0 mggF2Yp2x1
  have hdec1 : mggDecode hm v1 = (x, y + x + x + 1) := by
    rw [hv1, mggDecode_encode]
  change mggF2Neighbor hm v1 mggF2Ym2x = mggEncode hm (x, y + 1)
  rw [mggF2Neighbor_Ym2x_eq, hdec1]
  congr 1
  exact Prod.ext rfl (mggF2_fin_y_succ_cancel x y)

/-- One-step reachability in the x-direction (at most two labeled edges). -/
theorem mggF2_reachable_x_succ {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x + ⟨1, hm⟩, y)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggF2NeZero hm0
  set v0 := mggEncode hm0 (x, y)
  set v1 := mggF2Neighbor hm0 v0 mggF2Xp2y1
  set v2 := mggF2Neighbor hm0 v1 mggF2Xm2y
  have hone : (⟨1, hm⟩ : Fin m) = (1 : Fin m) :=
    Fin.ext (Nat.mod_eq_of_lt hm).symm
  have hv2 : v2 = mggEncode hm0 (x + ⟨1, hm⟩, y) := by
    simpa [hone] using mggF2_x_succ_via_shears hm0 x y
  have hreach : (mggF2Graph m hm0).Reachable v0 v2 := by
    by_cases h01 : v0 = v1
    · have hstep : v2 = mggF2Neighbor hm0 v0 mggF2Xm2y := by simp [v2, h01]
      have hne : mggF2Neighbor hm0 v0 mggF2Xm2y ≠ v0 := by
        intro heq
        have : mggEncode hm0 (x + ⟨1, hm⟩, y) = mggEncode hm0 (x, y) := by
          calc mggEncode hm0 (x + ⟨1, hm⟩, y) = v2 := hv2.symm
            _ = mggF2Neighbor hm0 v0 mggF2Xm2y := hstep
            _ = v0 := heq
            _ = mggEncode hm0 (x, y) := rfl
        have hx := (Prod.ext_iff.mp
          ((mggDecode_encode hm0 (x + ⟨1, hm⟩, y)).symm.trans
            ((congrArg (mggDecode hm0) this).trans
              (mggDecode_encode hm0 (x, y))))).1
        have hx1 : x + 1 = x := by simpa [hone] using hx
        exact Fin.add_one_ne_of_one_lt hm x hx1
      have hadj : (mggF2Graph m hm0).Adj v0 (mggF2Neighbor hm0 v0 mggF2Xm2y) :=
        mggF2_adj_of_neighbor_ne hm0 v0 mggF2Xm2y hne
      exact Relation.ReflTransGen.single (by simpa [hstep] using hadj)
    · by_cases h12 : v1 = v2
      · have hadj : (mggF2Graph m hm0).Adj v0 v1 :=
          mggF2_adj_of_neighbor_ne hm0 v0 mggF2Xp2y1 (Ne.symm h01)
        exact Relation.ReflTransGen.single (by simpa [h12] using hadj)
      · have hadj1 : (mggF2Graph m hm0).Adj v0 v1 :=
          mggF2_adj_of_neighbor_ne hm0 v0 mggF2Xp2y1 (Ne.symm h01)
        have hne2 : mggF2Neighbor hm0 v1 mggF2Xm2y ≠ v1 := by
          change v2 ≠ v1
          exact Ne.symm h12
        have hadj2 : (mggF2Graph m hm0).Adj v1 v2 :=
          mggF2_adj_of_neighbor_ne hm0 v1 mggF2Xm2y hne2
        exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj1) hadj2
  simpa [hv2] using hreach

/-- One-step reachability in the y-direction (at most two labeled edges). -/
theorem mggF2_reachable_y_succ {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y + ⟨1, hm⟩)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggF2NeZero hm0
  set v0 := mggEncode hm0 (x, y)
  set v1 := mggF2Neighbor hm0 v0 mggF2Yp2x1
  set v2 := mggF2Neighbor hm0 v1 mggF2Ym2x
  have hone : (⟨1, hm⟩ : Fin m) = (1 : Fin m) :=
    Fin.ext (Nat.mod_eq_of_lt hm).symm
  have hv2 : v2 = mggEncode hm0 (x, y + ⟨1, hm⟩) := by
    simpa [hone] using mggF2_y_succ_via_shears hm0 x y
  have hreach : (mggF2Graph m hm0).Reachable v0 v2 := by
    by_cases h01 : v0 = v1
    · have hstep : v2 = mggF2Neighbor hm0 v0 mggF2Ym2x := by simp [v2, h01]
      have hne : mggF2Neighbor hm0 v0 mggF2Ym2x ≠ v0 := by
        intro heq
        have : mggEncode hm0 (x, y + ⟨1, hm⟩) = mggEncode hm0 (x, y) := by
          calc mggEncode hm0 (x, y + ⟨1, hm⟩) = v2 := hv2.symm
            _ = mggF2Neighbor hm0 v0 mggF2Ym2x := hstep
            _ = v0 := heq
            _ = mggEncode hm0 (x, y) := rfl
        have hy := (Prod.ext_iff.mp
          ((mggDecode_encode hm0 (x, y + ⟨1, hm⟩)).symm.trans
            ((congrArg (mggDecode hm0) this).trans
              (mggDecode_encode hm0 (x, y))))).2
        have hy1 : y + 1 = y := by simpa [hone] using hy
        exact Fin.add_one_ne_of_one_lt hm y hy1
      have hadj : (mggF2Graph m hm0).Adj v0 (mggF2Neighbor hm0 v0 mggF2Ym2x) :=
        mggF2_adj_of_neighbor_ne hm0 v0 mggF2Ym2x hne
      exact Relation.ReflTransGen.single (by simpa [hstep] using hadj)
    · by_cases h12 : v1 = v2
      · have hadj : (mggF2Graph m hm0).Adj v0 v1 :=
          mggF2_adj_of_neighbor_ne hm0 v0 mggF2Yp2x1 (Ne.symm h01)
        exact Relation.ReflTransGen.single (by simpa [h12] using hadj)
      · have hadj1 : (mggF2Graph m hm0).Adj v0 v1 :=
          mggF2_adj_of_neighbor_ne hm0 v0 mggF2Yp2x1 (Ne.symm h01)
        have hne2 : mggF2Neighbor hm0 v1 mggF2Ym2x ≠ v1 := by
          change v2 ≠ v1
          exact Ne.symm h12
        have hadj2 : (mggF2Graph m hm0).Adj v1 v2 :=
          mggF2_adj_of_neighbor_ne hm0 v1 mggF2Ym2x hne2
        exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj1) hadj2
  simpa [hv2] using hreach

/-- `n` successive +1 steps in x. -/
theorem mggF2_reachable_right_pow {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    ∀ n : ℕ,
      (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
        (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
        (mggEncode (lt_trans Nat.zero_lt_one hm)
          (x + mggF2FinMod (lt_trans Nat.zero_lt_one hm) n, y)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggF2NeZero hm0
  intro n
  induction n with
  | zero =>
    have hx : x + mggF2FinMod hm0 0 = x := by
      apply Fin.ext
      simp [mggF2FinMod, Nat.zero_mod]
    simpa [hx] using
      (Relation.ReflTransGen.refl :
        (mggF2Graph m hm0).Reachable
          (mggEncode hm0 (x, y)) (mggEncode hm0 (x, y)))
  | succ n ih =>
    have hstep := mggF2_reachable_x_succ hm (x + mggF2FinMod hm0 n) y
    have heq :
        (x + mggF2FinMod hm0 n) + ⟨1, hm⟩ = x + mggF2FinMod hm0 (n + 1) := by
      apply Fin.ext
      simp only [mggF2FinMod, Fin.val_add]
      have hr : (n + 1) % m = (n % m + 1) % m := by
        calc (n + 1) % m
            = (n % m + 1 % m) % m := by rw [Nat.add_mod]
          _ = (n % m + 1) % m := by rw [Nat.mod_eq_of_lt hm]
      rw [hr]
      calc (((x.val + n % m) % m) + 1) % m
          = ((x.val + n % m) + 1) % m := by rw [Nat.mod_add_mod]
        _ = (x.val + (n % m + 1)) % m := by rw [Nat.add_assoc]
        _ = (x.val + (n % m + 1) % m) % m := by rw [Nat.add_mod_mod]
    exact Relation.ReflTransGen.trans ih (by simpa [heq] using hstep)

/-- `n` successive +1 steps in y. -/
theorem mggF2_reachable_up_pow {m : ℕ} (hm : 1 < m) (x y : Fin m) :
    ∀ n : ℕ,
      (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
        (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y))
        (mggEncode (lt_trans Nat.zero_lt_one hm)
          (x, y + mggF2FinMod (lt_trans Nat.zero_lt_one hm) n)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggF2NeZero hm0
  intro n
  induction n with
  | zero =>
    have hy : y + mggF2FinMod hm0 0 = y := by
      apply Fin.ext
      simp [mggF2FinMod, Nat.zero_mod]
    simpa [hy] using
      (Relation.ReflTransGen.refl :
        (mggF2Graph m hm0).Reachable
          (mggEncode hm0 (x, y)) (mggEncode hm0 (x, y)))
  | succ n ih =>
    have hstep := mggF2_reachable_y_succ hm x (y + mggF2FinMod hm0 n)
    have heq :
        (y + mggF2FinMod hm0 n) + ⟨1, hm⟩ = y + mggF2FinMod hm0 (n + 1) := by
      apply Fin.ext
      simp only [mggF2FinMod, Fin.val_add]
      have hr : (n + 1) % m = (n % m + 1) % m := by
        calc (n + 1) % m
            = (n % m + 1 % m) % m := by rw [Nat.add_mod]
          _ = (n % m + 1) % m := by rw [Nat.mod_eq_of_lt hm]
      rw [hr]
      calc (((y.val + n % m) % m) + 1) % m
          = ((y.val + n % m) + 1) % m := by rw [Nat.mod_add_mod]
        _ = (y.val + (n % m + 1)) % m := by rw [Nat.add_assoc]
        _ = (y.val + (n % m + 1) % m) % m := by rw [Nat.add_mod_mod]
    exact Relation.ReflTransGen.trans ih (by simpa [heq] using hstep)

/-- Same column: right walk from `x₁` to `x₂`. -/
theorem mggF2_reachable_right_to {m : ℕ} (hm : 1 < m) (x₁ x₂ y : Fin m) :
    (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x₁, y))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x₂, y)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggF2NeZero hm0
  have h := mggF2_reachable_right_pow hm x₁ y (x₂ - x₁).val
  have hx : x₁ + mggF2FinMod hm0 (x₂ - x₁).val = x₂ :=
    Fin.ext <| by
      have hlt : (x₂ - x₁).val < m := (x₂ - x₁).isLt
      simp [mggF2FinMod, Nat.mod_eq_of_lt hlt,
        congrArg Fin.val (add_sub_cancel x₁ x₂)]
  simpa [hx] using h

/-- Same row: up walk from `y₁` to `y₂`. -/
theorem mggF2_reachable_up_to {m : ℕ} (hm : 1 < m) (x y₁ y₂ : Fin m) :
    (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y₁))
      (mggEncode (lt_trans Nat.zero_lt_one hm) (x, y₂)) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  letI : NeZero m := mggF2NeZero hm0
  have h := mggF2_reachable_up_pow hm x y₁ (y₂ - y₁).val
  have hy : y₁ + mggF2FinMod hm0 (y₂ - y₁).val = y₂ :=
    Fin.ext <| by
      have hlt : (y₂ - y₁).val < m := (y₂ - y₁).isLt
      simp [mggF2FinMod, Nat.mod_eq_of_lt hlt,
        congrArg Fin.val (add_sub_cancel y₁ y₂)]
  simpa [hy] using h

/-- Any two encoded cells are reachable when `1 < m`. -/
theorem mggF2_reachable_encode {m : ℕ} (hm : 1 < m) (p q : Fin m × Fin m) :
    (mggF2Graph m (lt_trans Nat.zero_lt_one hm)).Reachable
      (mggEncode (lt_trans Nat.zero_lt_one hm) p)
      (mggEncode (lt_trans Nat.zero_lt_one hm) q) :=
  Relation.ReflTransGen.trans
    (mggF2_reachable_right_to hm p.1 q.1 p.2)
    (mggF2_reachable_up_to hm q.1 p.2 q.2)

/-- Factor-2 torus connectivity. Independent of `mggGraph_isConnected`. -/
theorem mggF2Graph_isConnected {m : ℕ} (hm : 0 < m) :
    (mggF2Graph m hm).IsConnected := by
  intro u v
  by_cases hm1 : 1 < m
  · rw [show u = mggEncode hm (mggDecode hm u) from (mggEncode_decode hm u).symm]
    rw [show v = mggEncode hm (mggDecode hm v) from (mggEncode_decode hm v).symm]
    convert mggF2_reachable_encode hm1 (mggDecode hm u) (mggDecode hm v)
  · have hm_eq : m = 1 := by omega
    subst hm_eq
    have huv : u = v := Fin.ext <|
      (Nat.lt_one_iff.mp u.isLt).trans (Nat.lt_one_iff.mp v.isLt).symm
    subst huv
    exact Relation.ReflTransGen.refl

end SATurday.ProofComplexity
