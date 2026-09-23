import Theory.ProofComplexity.MGG.Factor2
import Theory.ProofComplexity.MGG.Spectral
import Theory.ProofComplexity.MGG.GG.Rayleigh
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Factor-2 adjacency Rayleigh form (R2 Block A checklist item 2)

Real quadratic form of the eight Jimbo–Maruoka steps `mggF2Neighbor`.
`mggF2MultiRayleigh` has the same shape as unit-shear `mggMultiRayleigh`, but the
steps are the factor-2 shears. `MGGGabberGalil.ggAdj` is that same form, so
`gg_numerical_radius` applies to the centered indicator.

Cut identity: on a set indicator the form equals `8 · |S| - mggF2MultiCutCard`.
For a nonempty half-set this yields
`mggF2MultiCutCard ≥ ((8 - 5√2) / 2) · |S|`, hence `2 · |S| ≤ 5 · multiCut`.

The unit-shear surface (`mggNeighbor`, `mggMultiRayleigh`, `MggHasMultiCheeger`)
is not used as a hypothesis and is not rewritten.
LOG: R2 Block A factor-2 Rayleigh, cut identity, multi-Cheeger
-/

namespace SATurday.ProofComplexity

open Classical Finset BigOperators Real

/-! ## Coordinate values of the factor-2 steps -/

/-- `(x + 2y)` as a `Fin` value is addition of `2 * y.val` modulo `m`. -/
theorem mggF2_val_add_twice {m : ℕ} (_hm : 0 < m) (x y : Fin m) :
    (x + y + y).val = (x.val + 2 * y.val) % m := by
  have hy : y.val + y.val = 2 * y.val := by omega
  calc
    (x + y + y).val = ((x + y).val + y.val) % m := by simp [Fin.val_add]
    _ = ((x.val + y.val) % m + y.val) % m := by simp [Fin.val_add]
    _ = (x.val + y.val + y.val) % m := by rw [Nat.mod_add_mod]
    _ = (x.val + 2 * y.val) % m := by
      rw [show x.val + y.val + y.val = x.val + 2 * y.val from by rw [Nat.add_assoc, hy]]

/-- `(x + 2y + 1)` as a `Fin` value. -/
theorem mggF2_val_add_twice_succ {m : ℕ} [NeZero m] (hm : 0 < m) (x y : Fin m) :
    (x + y + y + 1).val = (x.val + (2 * y.val + 1)) % m := by
  calc
    (x + y + y + 1).val = ((x + y + y).val + (1 : Fin m).val) % m := by simp [Fin.val_add]
    _ = ((x.val + 2 * y.val) % m + 1 % m) % m := by
      rw [mggF2_val_add_twice hm x y]
      have hone : (1 : Fin m).val = 1 % m := by simp
      rw [hone]
    _ = (x.val + 2 * y.val + 1) % m :=
      (Nat.add_mod (x.val + 2 * y.val) 1 m).symm
    _ = (x.val + (2 * y.val + 1)) % m := by rw [Nat.add_assoc]

/-- Cast of a complement `m - t` is negation in `ZMod m`. -/
private theorem mggF2_zmod_sub {m : ℕ} (_hm : 0 < m) (t : ℕ) (ht : t ≤ m) :
    ((m - t : ℕ) : ZMod m) = - (t : ZMod m) := by
  rw [Nat.cast_sub ht, ZMod.natCast_self]
  simp

/-- `(x - 2y)` as a `Fin` value matches the Gabber–Galil inverse shift. -/
theorem mggF2_val_sub_twice {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    (x - y - y).val = (x.val + m - (2 * y.val) % m) % m := by
  let r := (2 * y.val) % m
  have hle : r ≤ x.val + m := by
    have hr : r < m := Nat.mod_lt _ hm
    omega
  have hyt : y.val ≤ m := le_of_lt y.isLt
  suffices hcast : ((x - y - y).val : ZMod m) =
      (((x.val + m - r) % m : ℕ) : ZMod m) by
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' (x - y - y).val ((x.val + m - r) % m) m).mp hcast
    rwa [Nat.mod_eq_of_lt (x - y - y).isLt, Nat.mod_eq_of_lt (Nat.mod_lt _ hm)] at hmod
  rw [Fin.val_sub (x - y) y, Fin.val_sub x y, ZMod.natCast_mod, Nat.cast_add,
    ZMod.natCast_mod, Nat.cast_add, mggF2_zmod_sub hm y.val hyt]
  have hright : (((x.val + m - r) % m : ℕ) : ZMod m) =
      (x.val : ZMod m) - (r : ZMod m) := by
    rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self]
    simp
  rw [hright]
  have hrcast : (r : ZMod m) = (2 : ZMod m) * (y.val : ZMod m) := by
    have : (r : ZMod m) = ((2 * y.val : ℕ) : ZMod m) := by
      simpa [r] using (ZMod.natCast_mod (2 * y.val) m).symm
    simpa [Nat.cast_mul] using this
  rw [hrcast]
  ring

/-- `(x - (2y + 1))` as a `Fin` value matches the Gabber–Galil inverse shift. -/
theorem mggF2_val_sub_twice_succ {m : ℕ} [NeZero m] (hm : 0 < m) (x y : Fin m) :
    (x - y - y - 1).val = (x.val + m - (2 * y.val + 1) % m) % m := by
  let r := (2 * y.val + 1) % m
  have hle : r ≤ x.val + m := by
    have hr : r < m := Nat.mod_lt _ hm
    omega
  have hone : ((1 : Fin m) : ℕ) ≤ m := le_of_lt (1 : Fin m).isLt
  suffices hcast : ((x - y - y - 1).val : ZMod m) =
      (((x.val + m - r) % m : ℕ) : ZMod m) by
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' (x - y - y - 1).val ((x.val + m - r) % m) m).mp hcast
    rwa [Nat.mod_eq_of_lt (x - y - y - 1).isLt, Nat.mod_eq_of_lt (Nat.mod_lt _ hm)] at hmod
  rw [Fin.val_sub (x - y - y) (1 : Fin m), ZMod.natCast_mod, Nat.cast_add,
    mggF2_zmod_sub hm ((1 : Fin m) : ℕ) hone]
  have hprev : ((x - y - y).val : ZMod m) = (x.val : ZMod m) - 2 * (y.val : ZMod m) := by
    have htwice := mggF2_val_sub_twice hm x y
    have hr0 : (2 * y.val) % m ≤ x.val + m := by
      have : (2 * y.val) % m < m := Nat.mod_lt _ hm
      omega
    rw [htwice, ZMod.natCast_mod, Nat.cast_sub hr0, Nat.cast_add, ZMod.natCast_self]
    simp [ZMod.natCast_mod, Nat.cast_mul]
  rw [hprev]
  have hright : (((x.val + m - r) % m : ℕ) : ZMod m) =
      (x.val : ZMod m) - (r : ZMod m) := by
    rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self]
    simp
  rw [hright]
  have hrcast : (r : ZMod m) = (2 : ZMod m) * (y.val : ZMod m) + 1 := by
    have : (r : ZMod m) = ((2 * y.val + 1 : ℕ) : ZMod m) := by
      simpa [r] using (ZMod.natCast_mod (2 * y.val + 1) m).symm
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have honeZ : ((1 : Fin m) : ZMod m) = 1 := by
    simp
  rw [hrcast, honeZ]
  ring

/-! ## Torus steps -/

/-- One labeled factor-2 step on torus coordinates. -/
def mggF2TorusStep (hm : 0 < m) (s : Fin 8) (p : MggTorus m) : MggTorus m :=
  mggDecode hm (mggF2Neighbor hm (mggEncode hm p) s)

theorem mggF2TorusStep_Xp2y {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xp2y (x, y) = (x + y + y, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Xp2y_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Xm2y {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xm2y (x, y) = (x - y - y, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Xm2y_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Yp2x {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Yp2x (x, y) = (x, y + x + x) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Yp2x_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Ym2x {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Ym2x (x, y) = (x, y - x - x) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Ym2x_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Xp2y1 {m : ℕ} [NeZero m] (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xp2y1 (x, y) = (x + y + y + 1, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Xp2y1_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Xm2y1 {m : ℕ} [NeZero m] (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xm2y1 (x, y) = (x - y - y - 1, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Xm2y1_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Yp2x1 {m : ℕ} [NeZero m] (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Yp2x1 (x, y) = (x, y + x + x + 1) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Yp2x1_eq]
  simp [mggDecode_encode]

theorem mggF2TorusStep_Ym2x1 {m : ℕ} [NeZero m] (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Ym2x1 (x, y) = (x, y - x - x - 1) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  unfold mggF2TorusStep
  rw [mggF2Neighbor_Ym2x1_eq]
  simp [mggDecode_encode]

/-- Horizontal `+2y` in the shape `ggShiftX` uses. -/
theorem mggF2TorusStep_Xp2y_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xp2y (x, y) =
      (⟨(x.val + 2 * y.val) % m, Nat.mod_lt _ hm⟩, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Xp2y]
  ext
  · exact mggF2_val_add_twice hm x y
  · rfl

/-- Horizontal `-(2y)` in the shape `ggAdj` uses. -/
theorem mggF2TorusStep_Xm2y_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xm2y (x, y) =
      (⟨(x.val + m - (2 * y.val) % m) % m, Nat.mod_lt _ hm⟩, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Xm2y]
  ext
  · exact mggF2_val_sub_twice hm x y
  · rfl

/-- Vertical `+2x` in the shape `ggShiftY` uses. -/
theorem mggF2TorusStep_Yp2x_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Yp2x (x, y) =
      (x, ⟨(y.val + 2 * x.val) % m, Nat.mod_lt _ hm⟩) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Yp2x]
  ext
  · rfl
  · exact mggF2_val_add_twice hm y x

/-- Vertical `-(2x)` in the shape `ggAdj` uses. -/
theorem mggF2TorusStep_Ym2x_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Ym2x (x, y) =
      (x, ⟨(y.val + m - (2 * x.val) % m) % m, Nat.mod_lt _ hm⟩) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Ym2x]
  ext
  · rfl
  · exact mggF2_val_sub_twice hm y x

/-- Horizontal `+(2y+1)` in the shape `ggShiftX` uses. -/
theorem mggF2TorusStep_Xp2y1_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xp2y1 (x, y) =
      (⟨(x.val + (2 * y.val + 1)) % m, Nat.mod_lt _ hm⟩, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Xp2y1]
  ext
  · exact mggF2_val_add_twice_succ hm x y
  · rfl

/-- Horizontal `-(2y+1)` in the shape `ggAdj` uses. -/
theorem mggF2TorusStep_Xm2y1_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Xm2y1 (x, y) =
      (⟨(x.val + m - (2 * y.val + 1) % m) % m, Nat.mod_lt _ hm⟩, y) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Xm2y1]
  ext
  · exact mggF2_val_sub_twice_succ hm x y
  · rfl

/-- Vertical `+(2x+1)` in the shape `ggShiftY` uses. -/
theorem mggF2TorusStep_Yp2x1_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Yp2x1 (x, y) =
      (x, ⟨(y.val + (2 * x.val + 1)) % m, Nat.mod_lt _ hm⟩) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Yp2x1]
  ext
  · rfl
  · exact mggF2_val_add_twice_succ hm y x

/-- Vertical `-(2x+1)` in the shape `ggAdj` uses. -/
theorem mggF2TorusStep_Ym2x1_mod {m : ℕ} (hm : 0 < m) (x y : Fin m) :
    mggF2TorusStep hm mggF2Ym2x1 (x, y) =
      (x, ⟨(y.val + m - (2 * x.val + 1) % m) % m, Nat.mod_lt _ hm⟩) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2TorusStep_Ym2x1]
  ext
  · rfl
  · exact mggF2_val_sub_twice_succ hm y x

/-! ## Inverses: each labeled step is a bijection -/

/-- Label inverse. Pairs `±2y`, `±(2y+1)`, `±2x`, `±(2x+1)`. -/
def mggF2InvGen (s : Fin 8) : Fin 8 :=
  if s = mggF2Xp2y then mggF2Xm2y
  else if s = mggF2Xm2y then mggF2Xp2y
  else if s = mggF2Yp2x then mggF2Ym2x
  else if s = mggF2Ym2x then mggF2Yp2x
  else if s = mggF2Xp2y1 then mggF2Xm2y1
  else if s = mggF2Xm2y1 then mggF2Xp2y1
  else if s = mggF2Yp2x1 then mggF2Ym2x1
  else mggF2Yp2x1

theorem mggF2InvGen_invGen (s : Fin 8) : mggF2InvGen (mggF2InvGen s) = s := by
  fin_cases s <;>
    simp [mggF2InvGen, mggF2Xp2y, mggF2Xm2y, mggF2Yp2x, mggF2Ym2x, mggF2Xp2y1,
      mggF2Xm2y1, mggF2Yp2x1, mggF2Ym2x1]

/-- Adding `2y` and then subtracting `2y` returns the start coordinate. -/
theorem mggF2_fin_add_twice_cancel {m : ℕ} [NeZero m] (x y : Fin m) :
    (x + y + y) - y - y = x := by
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Subtracting `2y` and then adding `2y` returns the start coordinate. -/
theorem mggF2_fin_sub_twice_cancel {m : ℕ} [NeZero m] (x y : Fin m) :
    (x - y - y) + y + y = x := by
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Subtracting `2y+1` and then adding `2y+1` returns the start coordinate. -/
theorem mggF2_fin_sub_twice_succ_cancel {m : ℕ} [NeZero m] (x y : Fin m) :
    (x - y - y - 1) + y + y + 1 = x := by
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Adding `2y+1` and then subtracting `2y+1` returns the start coordinate. -/
theorem mggF2_fin_add_twice_succ_cancel {m : ℕ} [NeZero m] (x y : Fin m) :
    (x + y + y + 1) - y - y - 1 = x := by
  calc
    (x + y + y + 1) - y - y - 1 = ((x + y + y + 1) - y - y) - 1 := by
      simp [sub_eq_add_neg, add_assoc]
    _ = (x + 1) - 1 := by rw [mggF2_fin_x_succ_cancel]
    _ = x := by simp

theorem mggF2TorusStep_inv {m : ℕ} (hm : 0 < m) (s : Fin 8) (p : MggTorus m) :
    mggF2TorusStep hm (mggF2InvGen s) (mggF2TorusStep hm s p) = p := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  fin_cases s
  · rw [show (⟨0, by decide⟩ : Fin 8) = mggF2Xp2y from rfl]
    rw [show mggF2InvGen mggF2Xp2y = mggF2Xm2y by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Xp2y, mggF2TorusStep_Xm2y]
    ext
    · exact congrArg Fin.val (mggF2_fin_add_twice_cancel p.1 p.2)
    · rfl
  · rw [show (⟨1, by decide⟩ : Fin 8) = mggF2Xm2y from rfl]
    rw [show mggF2InvGen mggF2Xm2y = mggF2Xp2y by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Xm2y, mggF2TorusStep_Xp2y]
    ext
    · exact congrArg Fin.val (mggF2_fin_sub_twice_cancel p.1 p.2)
    · rfl
  · rw [show (⟨2, by decide⟩ : Fin 8) = mggF2Yp2x from rfl]
    rw [show mggF2InvGen mggF2Yp2x = mggF2Ym2x by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Yp2x, mggF2TorusStep_Ym2x]
    ext
    · rfl
    · exact congrArg Fin.val (mggF2_fin_add_twice_cancel p.2 p.1)
  · rw [show (⟨3, by decide⟩ : Fin 8) = mggF2Ym2x from rfl]
    rw [show mggF2InvGen mggF2Ym2x = mggF2Yp2x by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Ym2x, mggF2TorusStep_Yp2x]
    ext
    · rfl
    · exact congrArg Fin.val (mggF2_fin_sub_twice_cancel p.2 p.1)
  · rw [show (⟨4, by decide⟩ : Fin 8) = mggF2Xp2y1 from rfl]
    rw [show mggF2InvGen mggF2Xp2y1 = mggF2Xm2y1 by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Xp2y1, mggF2TorusStep_Xm2y1]
    ext
    · exact congrArg Fin.val (mggF2_fin_add_twice_succ_cancel p.1 p.2)
    · rfl
  · rw [show (⟨5, by decide⟩ : Fin 8) = mggF2Xm2y1 from rfl]
    rw [show mggF2InvGen mggF2Xm2y1 = mggF2Xp2y1 by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Xm2y1, mggF2TorusStep_Xp2y1]
    ext
    · exact congrArg Fin.val (mggF2_fin_sub_twice_succ_cancel p.1 p.2)
    · rfl
  · rw [show (⟨6, by decide⟩ : Fin 8) = mggF2Yp2x1 from rfl]
    rw [show mggF2InvGen mggF2Yp2x1 = mggF2Ym2x1 by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Yp2x1, mggF2TorusStep_Ym2x1]
    ext
    · rfl
    · exact congrArg Fin.val (mggF2_fin_add_twice_succ_cancel p.2 p.1)
  · rw [show (⟨7, by decide⟩ : Fin 8) = mggF2Ym2x1 from rfl]
    rw [show mggF2InvGen mggF2Ym2x1 = mggF2Yp2x1 by unfold mggF2InvGen; decide]
    rw [mggF2TorusStep_Ym2x1, mggF2TorusStep_Yp2x1]
    ext
    · rfl
    · exact congrArg Fin.val (mggF2_fin_sub_twice_succ_cancel p.2 p.1)

theorem mggF2TorusStep_bijective {m : ℕ} (hm : 0 < m) (s : Fin 8) :
    Function.Bijective (mggF2TorusStep hm s) := by
  refine ⟨fun p q h => ?_, fun p => ⟨mggF2TorusStep hm (mggF2InvGen s) p, ?_⟩⟩
  · have hp := congrArg (mggF2TorusStep hm (mggF2InvGen s)) h
    simpa [mggF2TorusStep_inv hm] using hp
  · have h := mggF2TorusStep_inv hm (mggF2InvGen s) p
    simpa [mggF2InvGen_invGen] using h

theorem sum_mggF2TorusStep {m : ℕ} (hm : 0 < m) (s : Fin 8) (f : MggTorus m → ℝ) :
    (∑ p : MggTorus m, f (mggF2TorusStep hm s p)) = ∑ p : MggTorus m, f p :=
  Function.Bijective.sum_comp (mggF2TorusStep_bijective hm s) f

/-! ## Rayleigh form -/

/-- Factor-2 labeled adjacency form on torus coordinates. -/
noncomputable def mggF2MultiRayleigh (hm : 0 < m) (f : MggTorus m → ℝ) : ℝ :=
  ∑ p : MggTorus m, ∑ s : Fin 8, f p * f (mggF2TorusStep hm s p)

private theorem sum_mggF2_prod {m : ℕ} (body : MggTorus m → ℝ) :
    (∑ p : MggTorus m, body p) = ∑ x : Fin m, ∑ y : Fin m, body (x, y) :=
  Fintype.sum_prod_type body

private theorem sum_mggF2_label {m : ℕ} (hm : 0 < m) (f : MggTorus m → ℝ) (s : Fin 8)
    (coord : Fin m → Fin m → MggTorus m)
    (hc : ∀ x y, mggF2TorusStep hm s (x, y) = coord x y) :
    (∑ p : MggTorus m, f p * f (mggF2TorusStep hm s p)) =
      ∑ x : Fin m, ∑ y : Fin m, f (x, y) * f (coord x y) := by
  rw [sum_mggF2_prod]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [hc]

/-- `ggAdj` does not depend on which proof of `0 < n` is supplied. -/
theorem ggAdj_proof_irrel {n : ℕ} (h1 h2 : 0 < n) (g : Fin n → Fin n → ℝ) :
    MGGGabberGalil.ggAdj h1 g = MGGGabberGalil.ggAdj h2 g := by
  unfold MGGGabberGalil.ggAdj MGGGabberGalil.ggC1 MGGGabberGalil.ggC2
    MGGGabberGalil.ggShiftX MGGGabberGalil.ggShiftY
  congr

/-- The torus Rayleigh form is `ggAdj` of the matrix presentation. -/
theorem mggF2MultiRayleigh_eq_ggAdj {m : ℕ} (hm : 0 < m) (f : MggTorus m → ℝ) :
    mggF2MultiRayleigh hm f =
      MGGGabberGalil.ggAdj hm (fun x y => f (x, y)) := by
  classical
  unfold mggF2MultiRayleigh
  rw [Finset.sum_comm, Fin.sum_univ_eight]
  rw [show (0 : Fin 8) = mggF2Xp2y by decide,
    show (1 : Fin 8) = mggF2Xm2y by decide,
    show (2 : Fin 8) = mggF2Yp2x by decide,
    show (3 : Fin 8) = mggF2Ym2x by decide,
    show (4 : Fin 8) = mggF2Xp2y1 by decide,
    show (5 : Fin 8) = mggF2Xm2y1 by decide,
    show (6 : Fin 8) = mggF2Yp2x1 by decide,
    show (7 : Fin 8) = mggF2Ym2x1 by decide]
  rw [sum_mggF2_label hm f mggF2Xp2y _ (mggF2TorusStep_Xp2y_mod hm),
    sum_mggF2_label hm f mggF2Xm2y _ (mggF2TorusStep_Xm2y_mod hm),
    sum_mggF2_label hm f mggF2Yp2x _ (mggF2TorusStep_Yp2x_mod hm),
    sum_mggF2_label hm f mggF2Ym2x _ (mggF2TorusStep_Ym2x_mod hm),
    sum_mggF2_label hm f mggF2Xp2y1 _ (mggF2TorusStep_Xp2y1_mod hm),
    sum_mggF2_label hm f mggF2Xm2y1 _ (mggF2TorusStep_Xm2y1_mod hm),
    sum_mggF2_label hm f mggF2Yp2x1 _ (mggF2TorusStep_Yp2x1_mod hm),
    sum_mggF2_label hm f mggF2Ym2x1 _ (mggF2TorusStep_Ym2x1_mod hm)]
  unfold MGGGabberGalil.ggAdj MGGGabberGalil.ggC1 MGGGabberGalil.ggC2
    MGGGabberGalil.ggShiftX MGGGabberGalil.ggShiftY
  dsimp
  abel

/-- Staying labels at `v` are `8 - |mggF2LeavingGens|`. -/
theorem mggF2_staySum_eq_eight_sub_leaving (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) :
    (∑ s : Fin 8, if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0) =
      (8 : ℝ) - (mggF2LeavingGens hm S v).card := by
  classical
  have hleave : (mggF2LeavingGens hm S v).card ≤ 8 := by
    have := card_le_card (filter_subset (fun s => mggF2Neighbor hm v s ∉ S) univ)
    simpa [mggF2LeavingGens, card_univ, Fintype.card_fin] using this
  have hsum :
      (∑ s : Fin 8, if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0) =
        ((univ.filter fun s => mggF2Neighbor hm v s ∈ S).card : ℝ) := by
    simp
  have hdisj :
      Disjoint (univ.filter fun s => mggF2Neighbor hm v s ∈ S)
        (mggF2LeavingGens hm S v) := by
    refine disjoint_left.mpr ?_
    intro s hs hL
    exact (mem_mggF2LeavingGens_iff hm S v s).mp hL (mem_filter.mp hs).2
  have huniv :
      (univ.filter fun s => mggF2Neighbor hm v s ∈ S) ∪ mggF2LeavingGens hm S v = univ := by
    ext s
    simp [mem_mggF2LeavingGens_iff]
    exact Classical.em _
  have hcards :
      (univ.filter fun s => mggF2Neighbor hm v s ∈ S).card +
          (mggF2LeavingGens hm S v).card = 8 := by
    have := card_union_of_disjoint hdisj
    simpa [huniv, card_univ, Fintype.card_fin] using this.symm
  have hnat :
      (univ.filter fun s => mggF2Neighbor hm v s ∈ S).card =
        8 - (mggF2LeavingGens hm S v).card := by
    omega
  rw [hsum, hnat, Nat.cast_sub hleave]
  norm_cast

/-- Labeled staying mass is `8|S| - mggF2MultiCutCard`. -/
theorem mggF2MultiRayleigh_setIndicator {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiRayleigh hm (mggSetIndicator hm S) =
      (8 : ℝ) * S.card - mggF2MultiCutCard hm S := by
  classical
  unfold mggF2MultiRayleigh mggSetIndicator
  have hstep (s : Fin 8) (p : MggTorus m) :
      mggEncode hm (mggF2TorusStep hm s p) = mggF2Neighbor hm (mggEncode hm p) s := by
    simp [mggF2TorusStep, mggEncode_decode]
  simp_rw [hstep]
  have hre :=
    Function.Bijective.sum_comp (mggEncode_bijective hm)
      (fun v => ∑ s : Fin 8,
        (if v ∈ S then (1 : ℝ) else 0) *
          (if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0))
  have hsum :
      (∑ v : Fin (m * m), ∑ s : Fin 8,
          (if v ∈ S then (1 : ℝ) else 0) *
            (if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0)) =
        ∑ v ∈ S, ∑ s : Fin 8, if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0 := by
    have hpull (v : Fin (m * m)) :
        (∑ s : Fin 8,
            (if v ∈ S then (1 : ℝ) else 0) *
              (if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0)) =
          if v ∈ S then ∑ s : Fin 8, if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0 else 0 := by
      by_cases hv : v ∈ S <;> simp [hv]
    simp_rw [hpull]
    simp [sum_ite_mem, univ_inter]
  have hstay :
      (∑ v ∈ S, ∑ s : Fin 8, if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0) =
        ∑ v ∈ S, ((8 : ℝ) - (mggF2LeavingGens hm S v).card) := by
    refine sum_congr rfl fun v _ => ?_
    exact mggF2_staySum_eq_eight_sub_leaving hm S v
  have hcut :
      (∑ v ∈ S, ((8 : ℝ) - (mggF2LeavingGens hm S v).card)) =
        (8 : ℝ) * S.card - mggF2MultiCutCard hm S := by
    have hsub :
        (∑ v ∈ S, ((8 : ℝ) - ((mggF2LeavingGens hm S v).card : ℝ))) =
          ∑ v ∈ S, (8 : ℝ) -
            ∑ v ∈ S, ((mggF2LeavingGens hm S v).card : ℝ) := by
      simp [sum_sub_distrib]
    rw [hsub]
    have hcast :
        (∑ v ∈ S, ((mggF2LeavingGens hm S v).card : ℝ)) =
          (mggF2MultiCutCard hm S : ℝ) := by
      simpa [mggF2LeavingGens_card_sum hm S] using
        (Nat.cast_sum (s := S) (f := fun v => (mggF2LeavingGens hm S v).card)).symm
    rw [hcast]
    simp [sum_const, nsmul_eq_mul]
    ring
  calc
    (∑ p, ∑ s,
        (if mggEncode hm p ∈ S then (1 : ℝ) else 0) *
          (if mggF2Neighbor hm (mggEncode hm p) s ∈ S then (1 : ℝ) else 0))
        = ∑ v, ∑ s,
            (if v ∈ S then (1 : ℝ) else 0) *
              (if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0) := by
          simpa [mggDecode_encode hm] using hre
    _ = ∑ v ∈ S, ∑ s, if mggF2Neighbor hm v s ∈ S then (1 : ℝ) else 0 := hsum
    _ = ∑ v ∈ S, ((8 : ℝ) - (mggF2LeavingGens hm S v).card) := hstay
    _ = (8 : ℝ) * S.card - mggF2MultiCutCard hm S := hcut

/-- Indicator squares to itself. -/
theorem mggSetIndicator_sq {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : MggTorus m) :
    (mggSetIndicator hm S p) ^ 2 = mggSetIndicator hm S p := by
  unfold mggSetIndicator
  split_ifs <;> norm_num

/-- Squared norm of the centered indicator is `|S| (m² - |S|) / m²`. -/
theorem mggRealNormSq_centeredIndicator {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggRealNormSq (mggCenteredIndicator hm S) =
      (S.card : ℝ) * ((m * m : ℝ) - S.card) / (m * m : ℝ) := by
  classical
  unfold mggRealNormSq mggCenteredIndicator
  set f := mggSetIndicator hm S
  have hden : ((m * m : ℕ) : ℝ) = (m * m : ℝ) := by norm_cast
  simp_rw [hden]
  have hexp : ∀ p,
      (f p - (S.card : ℝ) / (m * m : ℝ)) ^ 2 =
        f p - 2 * ((S.card : ℝ) / (m * m : ℝ)) * f p +
          ((S.card : ℝ) / (m * m : ℝ)) ^ 2 := by
    intro p
    have hsq : (f p) ^ 2 = f p := by simpa [f] using mggSetIndicator_sq hm S p
    calc
      (f p - (S.card : ℝ) / (m * m : ℝ)) ^ 2
          = (f p) ^ 2 - 2 * f p * ((S.card : ℝ) / (m * m : ℝ)) +
              ((S.card : ℝ) / (m * m : ℝ)) ^ 2 := by ring
      _ = f p - 2 * ((S.card : ℝ) / (m * m : ℝ)) * f p +
            ((S.card : ℝ) / (m * m : ℝ)) ^ 2 := by rw [hsq]; ring
  simp_rw [hexp]
  set μ : ℝ := (S.card : ℝ) / (m * m : ℝ)
  rw [sum_add_distrib, sum_sub_distrib]
  rw [sum_mggSetIndicator hm]
  have hcross : (∑ p : MggTorus m, 2 * μ * f p) = 2 * μ * (S.card : ℝ) := by
    rw [← mul_sum, sum_mggSetIndicator hm]
  have hconst : (∑ p : MggTorus m, μ ^ 2) = (m * m : ℝ) * μ ^ 2 := by
    simp [sum_const, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin]
  rw [hcross, hconst]
  have hN : (m * m : ℝ) ≠ 0 := by
    have : m ≠ 0 := NeZero.out
    positivity
  simp only [μ]
  field_simp [hN]
  ring

/-- Centering subtracts `8 |S|² / m²` from the indicator Rayleigh form. -/
theorem mggF2MultiRayleigh_centered {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiRayleigh hm (mggCenteredIndicator hm S) =
      mggF2MultiRayleigh hm (mggSetIndicator hm S) -
        8 * (S.card : ℝ) ^ 2 / (m * m : ℝ) := by
  classical
  unfold mggF2MultiRayleigh mggCenteredIndicator
  set f := mggSetIndicator hm S
  have hden : ((m * m : ℕ) : ℝ) = (m * m : ℝ) := by norm_cast
  have hprod : ∀ p (s : Fin 8),
      (f p - (S.card : ℝ) / (m * m : ℝ)) *
          (f (mggF2TorusStep hm s p) - (S.card : ℝ) / (m * m : ℝ)) =
        f p * f (mggF2TorusStep hm s p) -
          ((S.card : ℝ) / (m * m : ℝ)) * f p -
          ((S.card : ℝ) / (m * m : ℝ)) * f (mggF2TorusStep hm s p) +
          ((S.card : ℝ) / (m * m : ℝ)) ^ 2 := by
    intro p s
    ring
  simp_rw [hden, hprod]
  set μ : ℝ := (S.card : ℝ) / (m * m : ℝ)
  have hinner (p : MggTorus m) :
      (∑ s : Fin 8,
          (f p * f (mggF2TorusStep hm s p) - μ * f p -
            μ * f (mggF2TorusStep hm s p) + μ ^ 2)) =
        (∑ s : Fin 8, f p * f (mggF2TorusStep hm s p)) -
          (∑ s : Fin 8, μ * f p) -
          (∑ s : Fin 8, μ * f (mggF2TorusStep hm s p)) +
          ∑ s : Fin 8, μ ^ 2 := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsplit :
      (∑ p : MggTorus m, ∑ s : Fin 8,
          (f p * f (mggF2TorusStep hm s p) - μ * f p -
            μ * f (mggF2TorusStep hm s p) + μ ^ 2)) =
        (∑ p : MggTorus m, ∑ s : Fin 8, f p * f (mggF2TorusStep hm s p)) -
          (∑ p : MggTorus m, ∑ s : Fin 8, μ * f p) -
          (∑ p : MggTorus m, ∑ s : Fin 8, μ * f (mggF2TorusStep hm s p)) +
          ∑ p : MggTorus m, ∑ s : Fin 8, μ ^ 2 := by
    simp_rw [hinner]
    rw [Finset.sum_add_distrib
      (f := fun p : MggTorus m =>
        (∑ s : Fin 8, f p * f (mggF2TorusStep hm s p)) -
          (∑ s : Fin 8, μ * f p) -
          (∑ s : Fin 8, μ * f (mggF2TorusStep hm s p)))
      (g := fun p : MggTorus m => ∑ s : Fin 8, μ ^ 2)]
    rw [Finset.sum_sub_distrib
      (f := fun p : MggTorus m =>
        (∑ s : Fin 8, f p * f (mggF2TorusStep hm s p)) -
          (∑ s : Fin 8, μ * f p))
      (g := fun p : MggTorus m => ∑ s : Fin 8, μ * f (mggF2TorusStep hm s p))]
    rw [Finset.sum_sub_distrib
      (f := fun p : MggTorus m => ∑ s : Fin 8, f p * f (mggF2TorusStep hm s p))
      (g := fun p : MggTorus m => ∑ s : Fin 8, μ * f p)]
  rw [hsplit]
  have hstay : (∑ p : MggTorus m, ∑ s : Fin 8, f p * f (mggF2TorusStep hm s p)) =
      mggF2MultiRayleigh hm f := by
    rfl
  have hown : (∑ p : MggTorus m, ∑ s : Fin 8, μ * f p) = 8 * μ * (S.card : ℝ) := by
    rw [Finset.sum_comm]
    have hpull : ∀ _s : Fin 8, (∑ p : MggTorus m, μ * f p) =
        μ * ∑ p : MggTorus m, f p := by
      intro _s
      exact (Finset.mul_sum (Finset.univ : Finset (MggTorus m)) f μ).symm
    have hL : (∑ s : Fin 8, ∑ p : MggTorus m, μ * f p) =
        ∑ s : Fin 8, μ * ∑ p : MggTorus m, f p := by
      refine Finset.sum_congr rfl fun s _ => hpull s
    rw [hL, sum_mggSetIndicator hm]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hshift : (∑ p : MggTorus m, ∑ s : Fin 8, μ * f (mggF2TorusStep hm s p)) =
      8 * μ * (S.card : ℝ) := by
    rw [Finset.sum_comm]
    have hpull : ∀ s : Fin 8,
        (∑ p : MggTorus m, μ * f (mggF2TorusStep hm s p)) =
          μ * ∑ p : MggTorus m, f (mggF2TorusStep hm s p) := by
      intro s
      exact (Finset.mul_sum (Finset.univ : Finset (MggTorus m))
        (fun p => f (mggF2TorusStep hm s p)) μ).symm
    have hL : (∑ s : Fin 8, ∑ p : MggTorus m, μ * f (mggF2TorusStep hm s p)) =
        ∑ s : Fin 8, μ * ∑ p : MggTorus m, f (mggF2TorusStep hm s p) := by
      refine Finset.sum_congr rfl fun s _ => hpull s
    rw [hL]
    have hstep : (∑ s : Fin 8, μ * ∑ p : MggTorus m, f (mggF2TorusStep hm s p)) =
        ∑ s : Fin 8, μ * ∑ p : MggTorus m, f p := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sum_mggF2TorusStep hm s]
    rw [hstep, sum_mggSetIndicator hm]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hconst : (∑ p : MggTorus m, ∑ s : Fin 8, μ ^ 2) = 8 * (m * m : ℝ) * μ ^ 2 := by
    rw [Finset.sum_comm]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    ring
  rw [hstay, hown, hshift, hconst]
  have hN : (m * m : ℝ) ≠ 0 := by
    have : m ≠ 0 := NeZero.out
    positivity
  simp only [μ]
  field_simp [hN]
  ring

/-- Centered Rayleigh form is `8 ‖g‖² - multiCut`. -/
theorem mggF2_centered_eq_eight_norm_sub_cut {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiRayleigh hm (mggCenteredIndicator hm S) =
      8 * mggRealNormSq (mggCenteredIndicator hm S) -
        (mggF2MultiCutCard hm S : ℝ) := by
  rw [mggF2MultiRayleigh_centered hm S, mggF2MultiRayleigh_setIndicator hm S,
    mggRealNormSq_centeredIndicator hm S]
  have hN : (m * m : ℝ) ≠ 0 := by
    have : m ≠ 0 := NeZero.out
    positivity
  field_simp [hN]
  ring

/-- `gg_numerical_radius` on the centered indicator. -/
theorem mggF2_centered_numerical_radius {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    |mggF2MultiRayleigh (lt_of_lt_of_le (by decide : 0 < 3) hm)
        (mggCenteredIndicator (lt_of_lt_of_le (by decide : 0 < 3) hm) S)| ≤
      5 * Real.sqrt 2 *
        mggRealNormSq
          (mggCenteredIndicator (lt_of_lt_of_le (by decide : 0 < 3) hm) S) := by
  let hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  let g : Fin m → Fin m → ℝ := fun x y => mggCenteredIndicator hm0 S (x, y)
  have hmean : ∑ x : Fin m, ∑ y : Fin m, g x y = 0 := by
    rw [← Fintype.sum_prod_type]
    simpa [g] using sum_mggCenteredIndicator hm0 S
  convert MGGGabberGalil.gg_numerical_radius hm g hmean using 1
  · rw [mggF2MultiRayleigh_eq_ggAdj hm0 (mggCenteredIndicator hm0 S)]
  · have hsq : mggRealNormSq (mggCenteredIndicator hm0 S) =
        ∑ x : Fin m, ∑ y : Fin m, (g x y) ^ 2 := by
      unfold mggRealNormSq
      rw [Fintype.sum_prod_type]
    rw [hsq]

/-- `(8 - 5√2) / 2 ≥ 2/5`, from `36² > 2 · 25²`. -/
theorem mggF2_cheeger_gap_ge_two_fifths :
    (2 : ℝ) / 5 ≤ (8 - 5 * Real.sqrt 2) / 2 := by
  have _hnat := mgg_cheeger_two_fifth_nat
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  have hsqrt : Real.sqrt 2 ≤ 36 / 25 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hmul : 25 * Real.sqrt 2 ≤ 36 := by
    have h := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 25)
    have : (25 : ℝ) * (36 / 25) = 36 := by norm_num
    linarith
  linarith

/-- For every set, `multiCut ≥ (8 - 5√2) · |S| · (m² - |S|) / m²`. -/
theorem mggF2MultiCut_ge_gap_mass {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) :
    (8 - 5 * Real.sqrt 2) *
        ((S.card : ℝ) * ((m * m : ℝ) - S.card) / (m * m : ℝ)) ≤
      (mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S : ℝ) := by
  let hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have hgap := mggF2_centered_eq_eight_norm_sub_cut hm0 S
  have hrad := mggF2_centered_numerical_radius hm S
  have hnorm := mggRealNormSq_centeredIndicator hm0 S
  have hle : mggF2MultiRayleigh hm0 (mggCenteredIndicator hm0 S) ≤
      5 * Real.sqrt 2 * mggRealNormSq (mggCenteredIndicator hm0 S) :=
    le_trans (le_abs_self _) hrad
  have hcut : (mggF2MultiCutCard hm0 S : ℝ) ≤
      8 * mggRealNormSq (mggCenteredIndicator hm0 S) -
        mggF2MultiRayleigh hm0 (mggCenteredIndicator hm0 S) := by
    linarith [hgap]
  have : (mggF2MultiCutCard hm0 S : ℝ) ≥
      (8 - 5 * Real.sqrt 2) * mggRealNormSq (mggCenteredIndicator hm0 S) := by
    linarith
  simpa [hm0, hnorm] using this

/-- Nonempty half-sets expand by at least `((8 - 5√2) / 2) · |S|`. -/
theorem mggF2MultiCut_ge_half_gap {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (_hne : S.Nonempty) (hhalf : 2 * S.card ≤ m * m) :
    ((8 - 5 * Real.sqrt 2) / 2) * (S.card : ℝ) ≤
      (mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S : ℝ) := by
  letI : NeZero m := ⟨by omega⟩
  have hmass := mggF2MultiCut_ge_gap_mass hm S
  set s : ℝ := (S.card : ℝ)
  set N : ℝ := m * m
  have hhalfR : 2 * s ≤ N := by
    have hcast : (2 : ℝ) * (S.card : ℝ) ≤ (m * m : ℝ) := by exact_mod_cast hhalf
    simpa [s, N] using hcast
  have hNpos : 0 < N := by
    have : (0 : ℕ) < m := by omega
    positivity
  have hratio : (1 : ℝ) / 2 ≤ (N - s) / N := by
    rw [le_div_iff₀ hNpos]
    linarith
  have hgap0 : 0 ≤ 8 - 5 * Real.sqrt 2 := by
    have h := mggF2_cheeger_gap_ge_two_fifths
    linarith
  have hs0 : 0 ≤ s := by positivity
  have hnorm_ge : ((8 - 5 * Real.sqrt 2) / 2) * s ≤
      (8 - 5 * Real.sqrt 2) * (s * (N - s) / N) := by
    calc
      ((8 - 5 * Real.sqrt 2) / 2) * s
          = (8 - 5 * Real.sqrt 2) * s * (1 / 2) := by ring
      _ ≤ (8 - 5 * Real.sqrt 2) * s * ((N - s) / N) := by
          gcongr
      _ = (8 - 5 * Real.sqrt 2) * (s * (N - s) / N) := by ring
  have hmass' : (8 - 5 * Real.sqrt 2) * (s * ((m * m : ℝ) - s) / (m * m : ℝ)) ≤
      (mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S : ℝ) := by
    simpa [s, N] using hmass
  exact hnorm_ge.trans hmass'

/-- Half-set numerical gap implies the Nat Cheeger form `2|S| ≤ 5 · multiCut`. -/
theorem mggF2_two_card_le_five_multiCut {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (hne : S.Nonempty) (hhalf : 2 * S.card ≤ m * m) :
    2 * S.card ≤ 5 * mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S := by
  have hcut := mggF2MultiCut_ge_half_gap hm S hne hhalf
  have hconst := mggF2_cheeger_gap_ge_two_fifths
  have hs0 : (0 : ℝ) ≤ S.card := by positivity
  have h25 : (2 : ℝ) / 5 * (S.card : ℝ) ≤
      (mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hconst hs0
    exact hmul.trans hcut
  have hreal : (2 : ℝ) * (S.card : ℝ) ≤
      5 * (mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left h25 (by norm_num : (0 : ℝ) ≤ 5)
    have : (5 : ℝ) * ((2 / 5) * (S.card : ℝ)) = 2 * (S.card : ℝ) := by ring
    linarith
  exact_mod_cast hreal

/-- Factor-2 multi-cut Cheeger at rate `2/5`. Same shape as `MggHasMultiCheeger`,
on `mggF2MultiCutCard` rather than `mggMultiCutCard`. -/
def MggF2HasMultiCheeger (m : ℕ) (hm : 0 < m) : Prop :=
  ∀ S : Finset (Fin (m * m)),
    S.Nonempty → 2 * S.card ≤ m * m →
      2 * S.card ≤ 5 * mggF2MultiCutCard hm S

/-- Gabber–Galil radius yields factor-2 multi Cheeger for every `m ≥ 3`. -/
theorem mggF2_hasMultiCheeger {m : ℕ} (hm : 3 ≤ m) :
    MggF2HasMultiCheeger m (lt_of_lt_of_le (by decide : 0 < 3) hm) := by
  intro S hne hhalf
  exact mggF2_two_card_le_five_multiCut hm S hne hhalf

/-- `mggInformativeFloor = 6` supplies `m ≥ 3`, so the same Cheeger prop holds.
`mgg_card_le_three_mul_multiCut_of_cheeger` stays on the unit-shear cut; the
factor-2 cut uses `mgg_card_le_three_mul_of_two_fifth` directly. -/
theorem mggF2_card_le_three_mul_multiCut_of_cheeger {m : ℕ} (hm : 0 < m)
    (h : MggF2HasMultiCheeger m hm) (S : Finset (Fin (m * m)))
    (hne : S.Nonempty) (hhalf : 2 * S.card ≤ m * m) :
    S.card ≤ 3 * mggF2MultiCutCard hm S :=
  mgg_card_le_three_mul_of_two_fifth (h S hne hhalf)

end SATurday.ProofComplexity
