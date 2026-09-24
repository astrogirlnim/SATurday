import Theory.ProofComplexity.MGG.Factor2Inv
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

/-!
# Factor-2 doubled edges live in two rows and two columns (R2 Block A item 3)

A simple edge of `mggF2Graph` carries two labels exactly when two distinct
generators of the same family (horizontal or vertical) produce the same
offset. Horizontal offsets in row `y` are `2y`, `-2y`, `2y+1`, `-(2y+1)`, so a
nonzero doubled offset forces `4y ≡ 0`, `4y+1 ≡ 0`, or `4y+2 ≡ 0 (mod m)`.

Main counting result: the set `mggF2DoubledOffsets m` of pairs
`(row, nonzero doubled offset)` has at most two elements, uniformly in `m`
(odd `m`: one row with two offsets; even `m`: two rows with offset `m/2`).
Consequently

- at most two rows and two columns carry any doubled edge
  (`mggF2SpecialLines_card_le_two`);
- at most `m` doubled horizontal and `m` doubled vertical edges cross any cut
  (`mggF2DoubledCutPairs_card_le_two_mul`);
- `mggF2MultiCutCard ≤ |edgeBoundary| + 2m`
  (`mggF2MultiCutCard_le_edgeBoundary_add_two_mul`).

The unit-shear loss lemmas of `MGG.lean` are not cited.

LOG: R2 Block A factor-2 doubled offsets, two special rows and columns, multiCut <= cut + 2m
-/

namespace SATurday.ProofComplexity

open Classical
open Finset
open Fin.CommRing

/-! ## Generic pair sets -/

/-- Pairs `(a, b)` with `a ∈ s` and `b ∈ F a`. -/
def mggF2Pairs {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (F : α → Finset β) : Finset (α × β) :=
  s.biUnion fun a => (F a).image fun b => (a, b)

theorem mem_mggF2Pairs_iff {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (F : α → Finset β)
    (p : α × β) : p ∈ mggF2Pairs s F ↔ p.1 ∈ s ∧ p.2 ∈ F p.1 := by
  simp only [mggF2Pairs, mem_biUnion, mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨p.1, ha, p.2, hb, rfl⟩

theorem mggF2Pairs_card {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (F : α → Finset β) :
    (mggF2Pairs s F).card = ∑ a ∈ s, (F a).card := by
  have hdisj : (s : Set α).PairwiseDisjoint fun a => (F a).image fun b => (a, b) := by
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
  rw [mggF2Pairs, card_biUnion hdisj]
  exact sum_congr rfl fun a _ =>
    card_image_of_injective _ fun _ _ h => (Prod.ext_iff.mp h).2

/-! ## Offsets of the eight labels -/

/-- Horizontal offset added to `x` by a horizontal label in row `y`. -/
def mggF2HOffset {m : ℕ} [NeZero m] (y : Fin m) (s : Fin 8) : Fin m :=
  match s.val with
  | 0 => y + y
  | 1 => -(y + y)
  | 4 => y + y + 1
  | _ => -(y + y + 1)

theorem mggF2HOffset_Xp2y {m : ℕ} [NeZero m] (y : Fin m) :
    mggF2HOffset y mggF2Xp2y = y + y := rfl
theorem mggF2HOffset_Xm2y {m : ℕ} [NeZero m] (y : Fin m) :
    mggF2HOffset y mggF2Xm2y = -(y + y) := rfl
theorem mggF2HOffset_Xp2y1 {m : ℕ} [NeZero m] (y : Fin m) :
    mggF2HOffset y mggF2Xp2y1 = y + y + 1 := rfl
theorem mggF2HOffset_Xm2y1 {m : ℕ} [NeZero m] (y : Fin m) :
    mggF2HOffset y mggF2Xm2y1 = -(y + y + 1) := rfl

/-- Relabel a vertical generator to the horizontal one with the same offset shape. -/
def mggF2VertToHoriz (s : Fin 8) : Fin 8 :=
  match s.val with
  | 2 => mggF2Xp2y
  | 3 => mggF2Xm2y
  | 6 => mggF2Xp2y1
  | _ => mggF2Xm2y1

theorem mggF2VertToHoriz_mem {s : Fin 8} (hs : s ∈ mggF2VertGens) :
    mggF2VertToHoriz s ∈ mggF2HorizGens := by
  rcases (mem_mggF2VertGens_iff s).mp hs with rfl | rfl | rfl | rfl <;> decide

theorem mggF2VertToHoriz_injOn {s t : Fin 8} (hs : s ∈ mggF2VertGens)
    (ht : t ∈ mggF2VertGens) (h : mggF2VertToHoriz s = mggF2VertToHoriz t) : s = t := by
  revert h
  rcases (mem_mggF2VertGens_iff s).mp hs with rfl | rfl | rfl | rfl <;>
    rcases (mem_mggF2VertGens_iff t).mp ht with rfl | rfl | rfl | rfl <;> decide

/-- Horizontal labels move `x` by `mggF2HOffset`. -/
theorem mggF2Neighbor_horiz_eq {m : ℕ} [NeZero m] (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggF2HorizGens) :
    mggF2Neighbor hm v s =
      mggEncode hm ((mggDecode hm v).1 + mggF2HOffset (mggDecode hm v).2 s,
        (mggDecode hm v).2) := by
  rcases (mem_mggF2HorizGens_iff s).mp hs with rfl | rfl | rfl | rfl
  · rw [mggF2Neighbor_Xp2y_eq, mggF2HOffset_Xp2y]
    congr 1
    exact Prod.ext (by dsimp only; ring) rfl
  · rw [mggF2Neighbor_Xp2y1_eq, mggF2HOffset_Xp2y1]
    congr 1
    exact Prod.ext (by dsimp only; ring) rfl
  · rw [mggF2Neighbor_Xm2y_eq, mggF2HOffset_Xm2y]
    congr 1
    exact Prod.ext (by dsimp only; ring) rfl
  · rw [mggF2Neighbor_Xm2y1_eq, mggF2HOffset_Xm2y1]
    congr 1
    exact Prod.ext (by dsimp only; ring) rfl

/-- Vertical labels move `y` by the relabeled horizontal offset of `x`. -/
theorem mggF2Neighbor_vert_eq {m : ℕ} [NeZero m] (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggF2VertGens) :
    mggF2Neighbor hm v s =
      mggEncode hm ((mggDecode hm v).1,
        (mggDecode hm v).2 + mggF2HOffset (mggDecode hm v).1 (mggF2VertToHoriz s)) := by
  rcases (mem_mggF2VertGens_iff s).mp hs with rfl | rfl | rfl | rfl
  · rw [mggF2Neighbor_Yp2x_eq]
    congr 1
    exact Prod.ext rfl (by dsimp only [mggF2VertToHoriz, mggF2Yp2x]; rw [mggF2HOffset_Xp2y]; ring)
  · rw [mggF2Neighbor_Yp2x1_eq]
    congr 1
    exact Prod.ext rfl
      (by dsimp only [mggF2VertToHoriz, mggF2Yp2x1]; rw [mggF2HOffset_Xp2y1]; ring)
  · rw [mggF2Neighbor_Ym2x_eq]
    congr 1
    exact Prod.ext rfl (by dsimp only [mggF2VertToHoriz, mggF2Ym2x]; rw [mggF2HOffset_Xm2y]; ring)
  · rw [mggF2Neighbor_Ym2x1_eq]
    congr 1
    exact Prod.ext rfl
      (by dsimp only [mggF2VertToHoriz, mggF2Ym2x1]; rw [mggF2HOffset_Xm2y1]; ring)

/-- The horizontal offset is the `x`-displacement of the neighbor. -/
theorem mggF2_hoffset_eq_sub {m : ℕ} [NeZero m] (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggF2HorizGens) :
    mggF2HOffset (mggDecode hm v).2 s =
      (mggDecode hm (mggF2Neighbor hm v s)).1 - (mggDecode hm v).1 := by
  rw [mggF2Neighbor_horiz_eq hm v hs, mggDecode_encode]
  exact (add_sub_cancel_left _ _).symm

/-- The vertical offset is the `y`-displacement of the neighbor. -/
theorem mggF2_voffset_eq_sub {m : ℕ} [NeZero m] (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggF2VertGens) :
    mggF2HOffset (mggDecode hm v).1 (mggF2VertToHoriz s) =
      (mggDecode hm (mggF2Neighbor hm v s)).2 - (mggDecode hm v).2 := by
  rw [mggF2Neighbor_vert_eq hm v hs, mggDecode_encode]
  exact (add_sub_cancel_left _ _).symm

/-! ## Doubled offsets -/

/-- Pairs `(row, nonzero offset)` realized by two distinct horizontal labels. The
same set governs columns, since vertical offsets are the same functions of `x`. -/
def mggF2DoubledOffsets (m : ℕ) [NeZero m] : Finset (Fin m × Fin m) :=
  (univ ×ˢ univ).filter fun p => p.2 ≠ 0 ∧
    ∃ s ∈ mggF2HorizGens, ∃ t ∈ mggF2HorizGens, s ≠ t ∧
      mggF2HOffset p.1 s = p.2 ∧ mggF2HOffset p.1 t = p.2

theorem mem_mggF2DoubledOffsets {m : ℕ} [NeZero m] {y δ : Fin m} :
    (y, δ) ∈ mggF2DoubledOffsets m ↔ δ ≠ 0 ∧
      ∃ s ∈ mggF2HorizGens, ∃ t ∈ mggF2HorizGens, s ≠ t ∧
        mggF2HOffset y s = δ ∧ mggF2HOffset y t = δ := by
  rw [mggF2DoubledOffsets, mem_filter]
  simp only [mem_product, mem_univ, true_and]

/-- Rows (equivalently columns) that carry a doubled edge. -/
def mggF2SpecialLines (m : ℕ) [NeZero m] : Finset (Fin m) :=
  (mggF2DoubledOffsets m).image Prod.fst

theorem mem_mggF2SpecialLines_of_doubled {m : ℕ} [NeZero m] {y δ : Fin m}
    (h : (y, δ) ∈ mggF2DoubledOffsets m) : y ∈ mggF2SpecialLines m :=
  mem_image.mpr ⟨(y, δ), h, rfl⟩

/-- Structural content of a doubled offset: the four collision patterns. -/
theorem mggF2DoubledOffsets_cases {m : ℕ} [NeZero m] (hm : 2 ≤ m) {y δ : Fin m}
    (h : (y, δ) ∈ mggF2DoubledOffsets m) :
    δ ≠ 0 ∧
      ((δ = y + y ∧ y + y + (y + y) = 0) ∨
       (δ = y + y ∧ y + y + (y + y) + 1 = 0) ∨
       (δ = y + y + 1 ∧ y + y + (y + y) + 1 = 0) ∨
       (δ = y + y + 1 ∧ y + y + (y + y) + 1 + 1 = 0)) := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨hδ, s, hs, t, ht, hst, hsδ, htδ⟩ := mem_mggF2DoubledOffsets.mp h
  refine ⟨hδ, ?_⟩
  have hplus : ∀ {a : Fin m}, a + 1 = a → False := fun {a} ha =>
    one_ne_zero (add_left_cancel (ha.trans (add_zero a).symm))
  rcases (mem_mggF2HorizGens_iff s).mp hs with rfl | rfl | rfl | rfl <;>
    rcases (mem_mggF2HorizGens_iff t).mp ht with rfl | rfl | rfl | rfl <;>
    simp only [mggF2HOffset_Xp2y, mggF2HOffset_Xp2y1, mggF2HOffset_Xm2y,
      mggF2HOffset_Xm2y1] at hsδ htδ
  · exact absurd rfl hst
  · exact (hplus (htδ.trans hsδ.symm)).elim
  · exact Or.inl ⟨hsδ.symm, by linear_combination hsδ - htδ⟩
  · exact Or.inr (Or.inl ⟨hsδ.symm, by linear_combination hsδ - htδ⟩)
  · exact (hplus (hsδ.trans htδ.symm)).elim
  · exact absurd rfl hst
  · exact Or.inr (Or.inr (Or.inl ⟨hsδ.symm, by linear_combination hsδ - htδ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hsδ.symm, by linear_combination hsδ - htδ⟩))
  · exact Or.inl ⟨htδ.symm, by linear_combination htδ - hsδ⟩
  · exact Or.inr (Or.inr (Or.inl ⟨htδ.symm, by linear_combination htδ - hsδ⟩))
  · exact absurd rfl hst
  · exact (hplus (neg_inj.mp (htδ.trans hsδ.symm))).elim
  · exact Or.inr (Or.inl ⟨htδ.symm, by linear_combination htδ - hsδ⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨htδ.symm, by linear_combination htδ - hsδ⟩))
  · exact (hplus (neg_inj.mp (hsδ.trans htδ.symm))).elim
  · exact absurd rfl hst

/-! ## Residue arithmetic in `Fin m` -/

theorem mggF2_val_add_modEq {m : ℕ} [NeZero m] (a b : Fin m) :
    (a + b).val ≡ a.val + b.val [MOD m] := by
  rw [Fin.val_add]
  exact Nat.mod_modEq _ _

theorem mggF2_val_one_modEq {m : ℕ} [NeZero m] : (1 : Fin m).val ≡ 1 [MOD m] := by
  rw [Fin.val_one']
  exact Nat.mod_modEq _ _

theorem mggF2_val_two_modEq {m : ℕ} [NeZero m] (y : Fin m) :
    (y + y).val ≡ 2 * y.val [MOD m] := by
  rw [two_mul]
  exact mggF2_val_add_modEq y y

theorem mggF2_val_two_one_modEq {m : ℕ} [NeZero m] (y : Fin m) :
    (y + y + 1).val ≡ 2 * y.val + 1 [MOD m] :=
  (mggF2_val_add_modEq _ 1).trans ((mggF2_val_two_modEq y).add mggF2_val_one_modEq)

theorem mggF2_val_four_modEq {m : ℕ} [NeZero m] (y : Fin m) :
    (y + y + (y + y)).val ≡ 4 * y.val [MOD m] := by
  have h := (mggF2_val_add_modEq (y + y) (y + y)).trans
    ((mggF2_val_two_modEq y).add (mggF2_val_two_modEq y))
  rwa [show 2 * y.val + 2 * y.val = 4 * y.val by ring] at h

theorem mggF2_val_four_one_modEq {m : ℕ} [NeZero m] (y : Fin m) :
    (y + y + (y + y) + 1).val ≡ 4 * y.val + 1 [MOD m] :=
  (mggF2_val_add_modEq _ 1).trans ((mggF2_val_four_modEq y).add mggF2_val_one_modEq)

/-- Even `m`: `4y + 1` never vanishes. -/
theorem mggF2_four_add_one_ne_zero_of_even {m : ℕ} [NeZero m] (hm : m % 2 = 0)
    (y : Fin m) : y + y + (y + y) + 1 ≠ 0 := by
  intro h
  have h1 := mggF2_val_four_one_modEq y
  rw [h, Fin.val_zero] at h1
  have h2 := Nat.ModEq.of_dvd (Nat.dvd_of_mod_eq_zero hm) h1
  unfold Nat.ModEq at h2
  omega

/-- Even `m`: an even residue never equals an odd one. -/
theorem mggF2_two_ne_two_add_one_of_even {m : ℕ} [NeZero m] (hm : m % 2 = 0)
    (y y' : Fin m) : y + y ≠ y' + y' + 1 := by
  intro h
  have h1 := mggF2_val_two_modEq y
  have h2 := mggF2_val_two_one_modEq y'
  rw [h] at h1
  have h3 := Nat.ModEq.of_dvd (Nat.dvd_of_mod_eq_zero hm) (h1.symm.trans h2)
  unfold Nat.ModEq at h3
  omega

/-- `z + z = 0` forces `z.val + z.val ∈ {0, m}`. -/
theorem mggF2_val_cases_of_add_self_eq_zero {m : ℕ} [NeZero m] (z : Fin m)
    (h : z + z = 0) : z.val + z.val = 0 ∨ z.val + z.val = m := by
  have h1 := mggF2_val_add_modEq z z
  rw [h, Fin.val_zero] at h1
  obtain ⟨q, hq⟩ := Nat.modEq_zero_iff_dvd.mp h1.symm
  have hz := z.isLt
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · interval_cases q <;> omega
  · have := Nat.mul_le_mul_left m hq2
    omega

/-- Odd `m`: `2` is invertible, so `z + z = 0` forces `z = 0`. -/
theorem mggF2_eq_zero_of_add_self_eq_zero_of_odd {m : ℕ} [NeZero m] (hm : m % 2 = 1)
    (z : Fin m) (h : z + z = 0) : z = 0 := by
  rcases mggF2_val_cases_of_add_self_eq_zero z h with h1 | h1
  · exact Fin.ext (by rw [Fin.val_zero]; omega)
  · omega

theorem mggF2_eq_zero_of_four_eq_zero_of_odd {m : ℕ} [NeZero m] (hm : m % 2 = 1)
    (y : Fin m) (h : y + y + (y + y) = 0) : y = 0 :=
  mggF2_eq_zero_of_add_self_eq_zero_of_odd hm y
    (mggF2_eq_zero_of_add_self_eq_zero_of_odd hm (y + y) h)

/-- Odd `m`: the row with `4y + 1 = 0` is unique. -/
theorem mggF2_four_add_one_unique_of_odd {m : ℕ} [NeZero m] (hm : m % 2 = 1)
    {y y' : Fin m} (h : y + y + (y + y) + 1 = 0) (h' : y' + y' + (y' + y') + 1 = 0) :
    y = y' := by
  have h4 : (y - y') + (y - y') + ((y - y') + (y - y')) = 0 := by
    linear_combination h - h'
  exact sub_eq_zero.mp (mggF2_eq_zero_of_four_eq_zero_of_odd hm _ h4)

/-- Nonzero elements of order two coincide. -/
theorem mggF2_order_two_unique {m : ℕ} [NeZero m] {δ δ' : Fin m} (hδ : δ ≠ 0)
    (hδ' : δ' ≠ 0) (h : δ + δ = 0) (h' : δ' + δ' = 0) : δ = δ' := by
  have hv : δ.val ≠ 0 := fun h0 => hδ (Fin.ext (by rw [Fin.val_zero]; exact h0))
  have hv' : δ'.val ≠ 0 := fun h0 => hδ' (Fin.ext (by rw [Fin.val_zero]; exact h0))
  rcases mggF2_val_cases_of_add_self_eq_zero δ h with h1 | h1 <;>
    rcases mggF2_val_cases_of_add_self_eq_zero δ' h' with h2 | h2
  · omega
  · omega
  · omega
  · exact Fin.ext (by omega)

/-- `2y = 2y'` gives `y' = y` or `y' = y + δ` for the order-two element `δ`. -/
theorem mggF2_eq_or_eq_add_of_two_eq {m : ℕ} [NeZero m] {y y' δ : Fin m} (hδ : δ ≠ 0)
    (hδ2 : δ + δ = 0) (h : y + y = y' + y') : y' = y ∨ y' = y + δ := by
  have hd : (y' - y) + (y' - y) = 0 := by linear_combination -h
  have hδv : δ.val ≠ 0 := fun h0 => hδ (Fin.ext (by rw [Fin.val_zero]; exact h0))
  rcases mggF2_val_cases_of_add_self_eq_zero (y' - y) hd with h1 | h1
  · left
    have : y' - y = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    exact sub_eq_zero.mp this
  · right
    rcases mggF2_val_cases_of_add_self_eq_zero δ hδ2 with h2 | h2
    · omega
    · have : y' - y = δ := Fin.ext (by omega)
      exact sub_eq_iff_eq_add'.mp this

/-- A finset all of whose elements are `p` or `f p` for any member `p` has at most
two elements. -/
theorem mggF2_card_le_two_of_forall {α : Type*} (P : Finset α) (f : α → α)
    (h : ∀ p ∈ P, ∀ q ∈ P, q = p ∨ q = f p) : P.card ≤ 2 := by
  rcases P.eq_empty_or_nonempty with hP | ⟨p, hp⟩
  · simp [hP]
  · have hsub : P ⊆ {p, f p} := by
      intro q hq
      rcases h p hp q hq with rfl | rfl <;> simp
    exact (card_le_card hsub).trans (card_le_two)

/-- Even `m`: every doubled offset has order two and is `2y` or `2y + 1`. -/
theorem mggF2DoubledOffsets_even {m : ℕ} [NeZero m] (hm : 2 ≤ m) (hpar : m % 2 = 0)
    {y δ : Fin m} (h : (y, δ) ∈ mggF2DoubledOffsets m) :
    δ ≠ 0 ∧ δ + δ = 0 ∧ (δ = y + y ∨ δ = y + y + 1) := by
  obtain ⟨hδ, hc⟩ := mggF2DoubledOffsets_cases hm h
  refine ⟨hδ, ?_⟩
  rcases hc with ⟨rfl, h4⟩ | ⟨_, h4⟩ | ⟨_, h4⟩ | ⟨rfl, h4⟩
  · exact ⟨h4, Or.inl rfl⟩
  · exact absurd h4 (mggF2_four_add_one_ne_zero_of_even hpar y)
  · exact absurd h4 (mggF2_four_add_one_ne_zero_of_even hpar y)
  · exact ⟨by linear_combination h4, Or.inr rfl⟩

/-- Odd `m`: every doubled offset sits in the row `4y + 1 = 0` and is `2y` or `2y + 1`. -/
theorem mggF2DoubledOffsets_odd {m : ℕ} [NeZero m] (hm : 2 ≤ m) (hpar : m % 2 = 1)
    {y δ : Fin m} (h : (y, δ) ∈ mggF2DoubledOffsets m) :
    y + y + (y + y) + 1 = 0 ∧ (δ = y + y ∨ δ = y + y + 1) := by
  obtain ⟨hδ, hc⟩ := mggF2DoubledOffsets_cases hm h
  rcases hc with ⟨rfl, h4⟩ | ⟨rfl, h4⟩ | ⟨rfl, h4⟩ | ⟨rfl, h4⟩
  · have hy : y = 0 := mggF2_eq_zero_of_four_eq_zero_of_odd hpar y h4
    exact absurd (by rw [hy, add_zero]) hδ
  · exact ⟨h4, Or.inl rfl⟩
  · exact ⟨h4, Or.inr rfl⟩
  · have h2 : (y + y + 1) + (y + y + 1) = 0 := by linear_combination h4
    exact absurd (mggF2_eq_zero_of_add_self_eq_zero_of_odd hpar _ h2) hδ

/-- The doubled offsets form a set of at most two pairs, uniformly in `m`. -/
theorem mggF2DoubledOffsets_card_le_two {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    (mggF2DoubledOffsets m).card ≤ 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with hpar | hpar
  · refine mggF2_card_le_two_of_forall _ (fun p => (p.1 + p.2, p.2)) ?_
    rintro ⟨y, δ⟩ hp ⟨y', δ'⟩ hq
    obtain ⟨hδ, hδ2, hcy⟩ := mggF2DoubledOffsets_even hm hpar hp
    obtain ⟨hδ', hδ2', hcy'⟩ := mggF2DoubledOffsets_even hm hpar hq
    have hδδ : δ' = δ := mggF2_order_two_unique hδ' hδ hδ2' hδ2
    subst hδδ
    have h2 : y + y = y' + y' := by
      rcases hcy with h1 | h1 <;> rcases hcy' with h2 | h2
      · exact h1.symm.trans h2
      · exact absurd (h1.symm.trans h2) (mggF2_two_ne_two_add_one_of_even hpar y y')
      · exact absurd (h2.symm.trans h1) (mggF2_two_ne_two_add_one_of_even hpar y' y)
      · exact add_right_cancel (h1.symm.trans h2)
    rcases mggF2_eq_or_eq_add_of_two_eq hδ hδ2 h2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · refine mggF2_card_le_two_of_forall _ (fun p => (p.1, -p.2)) ?_
    rintro ⟨y, δ⟩ hp ⟨y', δ'⟩ hq
    obtain ⟨h4, hcy⟩ := mggF2DoubledOffsets_odd hm hpar hp
    obtain ⟨h4', hcy'⟩ := mggF2DoubledOffsets_odd hm hpar hq
    have hyy : y = y' := mggF2_four_add_one_unique_of_odd hpar h4 h4'
    subst hyy
    rcases hcy with rfl | rfl <;> rcases hcy' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Prod.ext rfl (by dsimp only; linear_combination h4))
    · exact Or.inr (Prod.ext rfl (by dsimp only; linear_combination h4))
    · exact Or.inl rfl

theorem mggF2SpecialLines_card_le_two {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    (mggF2SpecialLines m).card ≤ 2 :=
  card_image_le.trans (mggF2DoubledOffsets_card_le_two hm)

/-! ## Fibers, doubled and non-doubled out-neighbors -/

/-- Labels at `v` reaching `w`. -/
def mggF2Fiber {m : ℕ} (hm : 0 < m) (v w : Fin (m * m)) : Finset (Fin 8) :=
  (univ : Finset (Fin 8)).filter fun s => mggF2Neighbor hm v s = w

theorem mggF2Fiber_card_le_two {m : ℕ} (hm : 0 < m) {v w : Fin (m * m)} (hne : w ≠ v) :
    (mggF2Fiber hm v w).card ≤ 2 :=
  mggF2_labels_to_ne_neighbor_card_le_two hm v w hne

/-- Out-neighbors reached by a single label. -/
def mggF2NdOut {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    Finset (Fin (m * m)) :=
  (mggF2OutNeighbors hm S v).filter fun w => (mggF2Fiber hm v w).card ≤ 1

/-- Out-neighbors reached by two labels. -/
def mggF2DblOut {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    Finset (Fin (m * m)) :=
  (mggF2OutNeighbors hm S v).filter fun w => ¬ (mggF2Fiber hm v w).card ≤ 1

theorem mggF2NdOut_card_add_dblOut_card {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) :
    (mggF2NdOut hm S v).card + (mggF2DblOut hm S v).card =
      (mggF2OutNeighbors hm S v).card :=
  card_filter_add_card_filter_not _

/-- Leaving labels are at most the out-degree plus the number of doubled targets. -/
theorem mggF2LeavingGens_card_le_out_add_dblOut {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S) :
    (mggF2LeavingGens hm S v).card ≤
      (mggF2OutNeighbors hm S v).card + (mggF2DblOut hm S v).card := by
  have hsum :
      (mggF2LeavingGens hm S v).card =
        ∑ w ∈ mggF2OutNeighbors hm S v,
          ((mggF2LeavingGens hm S v).filter fun s =>
            mggF2Neighbor hm v s = w).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro s hs
    simp only [mggF2OutNeighbors]
    exact mem_image.mpr ⟨s, hs, rfl⟩
  have hpt : ∀ w ∈ mggF2OutNeighbors hm S v,
      ((mggF2LeavingGens hm S v).filter fun s => mggF2Neighbor hm v s = w).card ≤
        1 + if ¬ (mggF2Fiber hm v w).card ≤ 1 then 1 else 0 := by
    intro w hw
    have hsub :
        (mggF2LeavingGens hm S v).filter (fun s => mggF2Neighbor hm v s = w) ⊆
          mggF2Fiber hm v w :=
      filter_subset_filter _ (subset_univ _)
    have hle := card_le_card hsub
    obtain ⟨_, _, hwn⟩ := (mem_mggF2OutNeighbors_iff hm S v w).mp hw
    have h2 := mggF2Fiber_card_le_two hm (mggF2Neighbor_ne_of_mem_not_mem hv hwn)
    split_ifs with h1 <;> omega
  calc
    (mggF2LeavingGens hm S v).card
        = ∑ w ∈ mggF2OutNeighbors hm S v,
            ((mggF2LeavingGens hm S v).filter fun s => mggF2Neighbor hm v s = w).card :=
          hsum
    _ ≤ ∑ w ∈ mggF2OutNeighbors hm S v,
          (1 + if ¬ (mggF2Fiber hm v w).card ≤ 1 then 1 else 0) := sum_le_sum hpt
    _ = (mggF2OutNeighbors hm S v).card + (mggF2DblOut hm S v).card := by
          rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, mggF2DblOut, card_filter]

/-- Multi-cut is at most out-degrees plus doubled targets. -/
theorem mggF2MultiCutCard_le_sum_out_add_dblOut {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiCutCard hm S ≤
      (∑ v ∈ S, (mggF2OutNeighbors hm S v).card) + ∑ v ∈ S, (mggF2DblOut hm S v).card := by
  rw [← mggF2LeavingGens_card_sum hm S, ← sum_add_distrib]
  exact sum_le_sum fun v hv => mggF2LeavingGens_card_le_out_add_dblOut hm S v hv

/-- Multi-cut plus non-doubled targets is at most twice the out-degrees. -/
theorem mggF2MultiCutCard_add_sum_ndOut_le {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiCutCard hm S + (∑ v ∈ S, (mggF2NdOut hm S v).card) ≤
      2 * ∑ v ∈ S, (mggF2OutNeighbors hm S v).card := by
  rw [← mggF2LeavingGens_card_sum hm S, ← sum_add_distrib, mul_sum]
  refine sum_le_sum fun v hv => ?_
  have h1 := mggF2LeavingGens_card_le_out_add_dblOut hm S v hv
  have h2 := mggF2NdOut_card_add_dblOut_card hm S v
  omega

/-! ## A doubled pair is horizontal or vertical -/

theorem mggF2_dblOut_horiz_or_vert {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    {v w : Fin (m * m)} (hv : v ∈ S) (hw : w ∈ mggF2DblOut hm S v) :
    w ≠ v ∧
      (((mggDecode hm w).2 = (mggDecode hm v).2 ∧
          ∃ s ∈ mggF2HorizGens, ∃ t ∈ mggF2HorizGens, s ≠ t ∧
            mggF2Neighbor hm v s = w ∧ mggF2Neighbor hm v t = w) ∨
        ((mggDecode hm w).1 = (mggDecode hm v).1 ∧
          ∃ s ∈ mggF2VertGens, ∃ t ∈ mggF2VertGens, s ≠ t ∧
            mggF2Neighbor hm v s = w ∧ mggF2Neighbor hm v t = w)) := by
  obtain ⟨hwo, hfib⟩ := mem_filter.mp hw
  obtain ⟨_, _, hwn⟩ := (mem_mggF2OutNeighbors_iff hm S v w).mp hwo
  have hne : w ≠ v := mggF2Neighbor_ne_of_mem_not_mem hv hwn
  refine ⟨hne, ?_⟩
  have h2 : 1 < (mggF2Fiber hm v w).card := by omega
  obtain ⟨s, hs, t, ht, hst⟩ := one_lt_card.mp h2
  have hsw : mggF2Neighbor hm v s = w := (mem_filter.mp hs).2
  have htw : mggF2Neighbor hm v t = w := (mem_filter.mp ht).2
  have hsne : mggF2Neighbor hm v s ≠ v := by rw [hsw]; exact hne
  have htne : mggF2Neighbor hm v t ≠ v := by rw [htw]; exact hne
  rcases mem_mggF2HorizGens_or_vert s with hsH | hsV
  · left
    have htH : t ∈ mggF2HorizGens := by
      rcases mem_mggF2HorizGens_or_vert t with htH | htV
      · exact htH
      · exact absurd (hsw.trans htw.symm)
          (mggF2Neighbor_horiz_ne_vert_of_ne_self hm v hsH htV hsne)
    exact ⟨by rw [← hsw]; exact mggF2Neighbor_horiz_same_y hm v hsH,
      s, hsH, t, htH, hst, hsw, htw⟩
  · right
    have htV : t ∈ mggF2VertGens := by
      rcases mem_mggF2HorizGens_or_vert t with htH | htV
      · exact absurd (htw.trans hsw.symm)
          (mggF2Neighbor_horiz_ne_vert_of_ne_self hm v htH hsV htne)
      · exact htV
    exact ⟨by rw [← hsw]; exact mggF2Neighbor_vert_same_x hm v hsV,
      s, hsV, t, htV, hst, hsw, htw⟩

/-- Two distinct horizontal labels to a common non-loop target give a doubled offset. -/
theorem mggF2_mem_doubledOffsets_of_horiz {m : ℕ} [NeZero m] (hm : 0 < m)
    {v w : Fin (m * m)} (hne : w ≠ v) {s t : Fin 8} (hs : s ∈ mggF2HorizGens)
    (ht : t ∈ mggF2HorizGens) (hst : s ≠ t) (hsw : mggF2Neighbor hm v s = w)
    (htw : mggF2Neighbor hm v t = w) :
    ((mggDecode hm v).2, (mggDecode hm w).1 - (mggDecode hm v).1) ∈
      mggF2DoubledOffsets m := by
  refine mem_mggF2DoubledOffsets.mpr ⟨?_, s, hs, t, ht, hst, ?_, ?_⟩
  · intro h0
    have hx : (mggDecode hm w).1 = (mggDecode hm v).1 := sub_eq_zero.mp h0
    have hy : (mggDecode hm w).2 = (mggDecode hm v).2 := by
      rw [← hsw]; exact mggF2Neighbor_horiz_same_y hm v hs
    exact hne (by
      rw [← mggEncode_decode hm w, ← mggEncode_decode hm v, Prod.ext hx hy])
  · rw [mggF2_hoffset_eq_sub hm v hs, hsw]
  · rw [mggF2_hoffset_eq_sub hm v ht, htw]

/-- Two distinct vertical labels to a common non-loop target give a doubled offset. -/
theorem mggF2_mem_doubledOffsets_of_vert {m : ℕ} [NeZero m] (hm : 0 < m)
    {v w : Fin (m * m)} (hne : w ≠ v) {s t : Fin 8} (hs : s ∈ mggF2VertGens)
    (ht : t ∈ mggF2VertGens) (hst : s ≠ t) (hsw : mggF2Neighbor hm v s = w)
    (htw : mggF2Neighbor hm v t = w) :
    ((mggDecode hm v).1, (mggDecode hm w).2 - (mggDecode hm v).2) ∈
      mggF2DoubledOffsets m := by
  refine mem_mggF2DoubledOffsets.mpr
    ⟨?_, mggF2VertToHoriz s, mggF2VertToHoriz_mem hs, mggF2VertToHoriz t,
      mggF2VertToHoriz_mem ht, fun h => hst (mggF2VertToHoriz_injOn hs ht h), ?_, ?_⟩
  · intro h0
    have hy : (mggDecode hm w).2 = (mggDecode hm v).2 := sub_eq_zero.mp h0
    have hx : (mggDecode hm w).1 = (mggDecode hm v).1 := by
      rw [← hsw]; exact mggF2Neighbor_vert_same_x hm v hs
    exact hne (by
      rw [← mggEncode_decode hm w, ← mggEncode_decode hm v, Prod.ext hx hy])
  · rw [mggF2_voffset_eq_sub hm v hs, hsw]
  · rw [mggF2_voffset_eq_sub hm v ht, htw]

/-- A horizontal single-label edge out of a non-special row is non-doubled. -/
theorem mggF2_fiber_card_le_one_of_horiz_not_special {m : ℕ} [NeZero m] (hm : 0 < m)
    {u w : Fin (m * m)} (hne : w ≠ u) {s : Fin 8} (hs : s ∈ mggF2HorizGens)
    (hsw : mggF2Neighbor hm u s = w) (hspec : (mggDecode hm u).2 ∉ mggF2SpecialLines m) :
    (mggF2Fiber hm u w).card ≤ 1 := by
  by_contra hcon
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (not_le.mp hcon)
  have haw : mggF2Neighbor hm u a = w := (mem_filter.mp ha).2
  have hbw : mggF2Neighbor hm u b = w := (mem_filter.mp hb).2
  have hsne : mggF2Neighbor hm u s ≠ u := by rw [hsw]; exact hne
  have hH : ∀ c : Fin 8, mggF2Neighbor hm u c = w → c ∈ mggF2HorizGens := by
    intro c hcw
    rcases mem_mggF2HorizGens_or_vert c with hcH | hcV
    · exact hcH
    · exact absurd (hsw.trans hcw.symm)
        (mggF2Neighbor_horiz_ne_vert_of_ne_self hm u hs hcV hsne)
  exact hspec (mem_mggF2SpecialLines_of_doubled
    (mggF2_mem_doubledOffsets_of_horiz hm hne (hH a haw) (hH b hbw) hab haw hbw))

/-- A vertical single-label edge out of a non-special column is non-doubled. -/
theorem mggF2_fiber_card_le_one_of_vert_not_special {m : ℕ} [NeZero m] (hm : 0 < m)
    {u w : Fin (m * m)} (hne : w ≠ u) {s : Fin 8} (hs : s ∈ mggF2VertGens)
    (hsw : mggF2Neighbor hm u s = w) (hspec : (mggDecode hm u).1 ∉ mggF2SpecialLines m) :
    (mggF2Fiber hm u w).card ≤ 1 := by
  by_contra hcon
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (not_le.mp hcon)
  have haw : mggF2Neighbor hm u a = w := (mem_filter.mp ha).2
  have hbw : mggF2Neighbor hm u b = w := (mem_filter.mp hb).2
  have hsne : mggF2Neighbor hm u s ≠ u := by rw [hsw]; exact hne
  have hV : ∀ c : Fin 8, mggF2Neighbor hm u c = w → c ∈ mggF2VertGens := by
    intro c hcw
    rcases mem_mggF2HorizGens_or_vert c with hcH | hcV
    · exact absurd (hcw.trans hsw.symm)
        (mggF2Neighbor_horiz_ne_vert_of_ne_self hm u hcH hs (by rw [hcw]; exact hne))
    · exact hcV
  exact hspec (mem_mggF2SpecialLines_of_doubled
    (mggF2_mem_doubledOffsets_of_vert hm hne (hV a haw) (hV b hbw) hab haw hbw))

/-! ## Doubled cut pairs number at most `2m` -/

/-- Directed doubled cut pairs `(v, w)`, `v ∈ S`, `w` a doubled out-neighbor. -/
def mggF2DoubledCutPairs {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin (m * m) × Fin (m * m)) :=
  mggF2Pairs S (mggF2DblOut hm S)

theorem mggF2DoubledCutPairs_card {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (mggF2DoubledCutPairs hm S).card = ∑ v ∈ S, (mggF2DblOut hm S v).card :=
  mggF2Pairs_card _ _

/-- Cells `x` of row `y` inside `S` whose `δ`-shift leaves `S`. -/
def mggF2RowCross {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m)))
    (p : Fin m × Fin m) : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun x =>
    mggEncode hm (x, p.1) ∈ S ∧ mggEncode hm (x + p.2, p.1) ∉ S

/-- Cells `y` of column `x` inside `S` whose `δ`-shift leaves `S`. -/
def mggF2ColCross {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m)))
    (p : Fin m × Fin m) : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun y =>
    mggEncode hm (p.1, y) ∈ S ∧ mggEncode hm (p.1, y + p.2) ∉ S

/-- Shifting a set of residues by a fixed offset stays inside the complement, so
crossing cells are at most half the line. -/
theorem mggF2RowCross_two_mul_card_le {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin m × Fin m) :
    2 * (mggF2RowCross hm S p).card ≤ m := by
  have h1 : (mggF2RowCross hm S p).card ≤
      ((univ : Finset (Fin m)).filter fun x => mggEncode hm (x, p.1) ∈ S).card :=
    card_le_card fun x hx => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.1⟩
  have h2 : (mggF2RowCross hm S p).card ≤
      ((univ : Finset (Fin m)).filter fun x => ¬ mggEncode hm (x, p.1) ∈ S).card := by
    refine card_le_card_of_injOn (fun x => x + p.2) ?_ ?_
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.2⟩
    · intro x _ x' _ h
      exact add_right_cancel h
  have h3 := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (fun x => mggEncode hm (x, p.1) ∈ S)
  rw [card_univ, Fintype.card_fin] at h3
  omega

theorem mggF2ColCross_two_mul_card_le {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin m × Fin m) :
    2 * (mggF2ColCross hm S p).card ≤ m := by
  have h1 : (mggF2ColCross hm S p).card ≤
      ((univ : Finset (Fin m)).filter fun y => mggEncode hm (p.1, y) ∈ S).card :=
    card_le_card fun y hy => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.1⟩
  have h2 : (mggF2ColCross hm S p).card ≤
      ((univ : Finset (Fin m)).filter fun y => ¬ mggEncode hm (p.1, y) ∈ S).card := by
    refine card_le_card_of_injOn (fun y => y + p.2) ?_ ?_
    · intro y hy
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.2⟩
    · intro y _ y' _ h
      exact add_right_cancel h
  have h3 := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m))) (fun y => mggEncode hm (p.1, y) ∈ S)
  rw [card_univ, Fintype.card_fin] at h3
  omega

/-- Horizontal doubled cut pairs inject into `(doubled offset, source column)`. -/
theorem mggF2_horiz_doubledCutPairs_card_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    ((mggF2DoubledCutPairs (lt_of_lt_of_le (by decide : 0 < 2) hm) S).filter fun q =>
        (mggDecode (lt_of_lt_of_le (by decide : 0 < 2) hm) q.2).2 =
          (mggDecode (lt_of_lt_of_le (by decide : 0 < 2) hm) q.1).2).card ≤ m := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  set T := mggF2Pairs (mggF2DoubledOffsets m) (mggF2RowCross hm0 S) with hT
  have hTcard : T.card = ∑ p ∈ mggF2DoubledOffsets m, (mggF2RowCross hm0 S p).card :=
    mggF2Pairs_card _ _
  have hTle : 2 * T.card ≤ 2 * m := by
    rw [hTcard, mul_sum]
    calc
      ∑ p ∈ mggF2DoubledOffsets m, 2 * (mggF2RowCross hm0 S p).card
          ≤ ∑ _p ∈ mggF2DoubledOffsets m, m :=
            sum_le_sum fun p _ => mggF2RowCross_two_mul_card_le hm0 S p
      _ = (mggF2DoubledOffsets m).card * m := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 * m := Nat.mul_le_mul_right m (mggF2DoubledOffsets_card_le_two hm)
  have hinj :
      ((mggF2DoubledCutPairs hm0 S).filter fun q =>
          (mggDecode hm0 q.2).2 = (mggDecode hm0 q.1).2).card ≤ T.card := by
    refine card_le_card_of_injOn
      (fun q => (((mggDecode hm0 q.1).2, (mggDecode hm0 q.2).1 - (mggDecode hm0 q.1).1),
        (mggDecode hm0 q.1).1)) ?_ ?_
    · intro q hq
      dsimp only
      obtain ⟨hqP, hqy⟩ := mem_filter.mp hq
      obtain ⟨hv, hw⟩ := (mem_mggF2Pairs_iff _ _ q).mp hqP
      obtain ⟨hne, hcase⟩ := mggF2_dblOut_horiz_or_vert hm0 S hv hw
      have hwn : q.2 ∉ S := by
        obtain ⟨_, _, h⟩ := (mem_mggF2OutNeighbors_iff hm0 S q.1 q.2).mp (mem_filter.mp hw).1
        exact h
      obtain ⟨s, hs, t, ht, hst, hsw, htw⟩ : ∃ s ∈ mggF2HorizGens, ∃ t ∈ mggF2HorizGens,
          s ≠ t ∧ mggF2Neighbor hm0 q.1 s = q.2 ∧ mggF2Neighbor hm0 q.1 t = q.2 := by
        rcases hcase with ⟨_, h⟩ | ⟨hx, _⟩
        · exact h
        · exact absurd (by
            rw [← mggEncode_decode hm0 q.2, ← mggEncode_decode hm0 q.1, Prod.ext hx hqy])
            hne
      refine (mem_mggF2Pairs_iff _ _ _).mpr ⟨?_, ?_⟩
      · exact mggF2_mem_doubledOffsets_of_horiz hm0 hne hs ht hst hsw htw
      · refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
        · rw [show ((mggDecode hm0 q.1).1, (mggDecode hm0 q.1).2) = mggDecode hm0 q.1 from
            rfl, mggEncode_decode]
          exact hv
        · rw [add_sub_cancel, ← hqy,
            show ((mggDecode hm0 q.2).1, (mggDecode hm0 q.2).2) = mggDecode hm0 q.2 from rfl,
            mggEncode_decode]
          exact hwn
    · intro q hq q' hq' h
      obtain ⟨_, hqy⟩ := mem_filter.mp hq
      obtain ⟨_, hqy'⟩ := mem_filter.mp hq'
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨hy, hδ⟩, hx⟩ := h
      have hv : q.1 = q'.1 := by
        rw [← mggEncode_decode hm0 q.1, ← mggEncode_decode hm0 q'.1, Prod.ext hx hy]
      have hxw : (mggDecode hm0 q.2).1 = (mggDecode hm0 q'.2).1 := by
        have := congrArg (fun z => z + (mggDecode hm0 q.1).1) hδ
        simpa [sub_add_cancel, hx] using this
      have hyw : (mggDecode hm0 q.2).2 = (mggDecode hm0 q'.2).2 := by
        rw [hqy, hqy', hy]
      have hw : q.2 = q'.2 := by
        rw [← mggEncode_decode hm0 q.2, ← mggEncode_decode hm0 q'.2, Prod.ext hxw hyw]
      exact Prod.ext hv hw
  omega

/-- Vertical doubled cut pairs inject into `(doubled offset, source row)`. -/
theorem mggF2_vert_doubledCutPairs_card_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    ((mggF2DoubledCutPairs (lt_of_lt_of_le (by decide : 0 < 2) hm) S).filter fun q =>
        (mggDecode (lt_of_lt_of_le (by decide : 0 < 2) hm) q.2).1 =
          (mggDecode (lt_of_lt_of_le (by decide : 0 < 2) hm) q.1).1).card ≤ m := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  set T := mggF2Pairs (mggF2DoubledOffsets m) (mggF2ColCross hm0 S) with hT
  have hTcard : T.card = ∑ p ∈ mggF2DoubledOffsets m, (mggF2ColCross hm0 S p).card :=
    mggF2Pairs_card _ _
  have hTle : 2 * T.card ≤ 2 * m := by
    rw [hTcard, mul_sum]
    calc
      ∑ p ∈ mggF2DoubledOffsets m, 2 * (mggF2ColCross hm0 S p).card
          ≤ ∑ _p ∈ mggF2DoubledOffsets m, m :=
            sum_le_sum fun p _ => mggF2ColCross_two_mul_card_le hm0 S p
      _ = (mggF2DoubledOffsets m).card * m := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 * m := Nat.mul_le_mul_right m (mggF2DoubledOffsets_card_le_two hm)
  have hinj :
      ((mggF2DoubledCutPairs hm0 S).filter fun q =>
          (mggDecode hm0 q.2).1 = (mggDecode hm0 q.1).1).card ≤ T.card := by
    refine card_le_card_of_injOn
      (fun q => (((mggDecode hm0 q.1).1, (mggDecode hm0 q.2).2 - (mggDecode hm0 q.1).2),
        (mggDecode hm0 q.1).2)) ?_ ?_
    · intro q hq
      dsimp only
      obtain ⟨hqP, hqx⟩ := mem_filter.mp hq
      obtain ⟨hv, hw⟩ := (mem_mggF2Pairs_iff _ _ q).mp hqP
      obtain ⟨hne, hcase⟩ := mggF2_dblOut_horiz_or_vert hm0 S hv hw
      have hwn : q.2 ∉ S := by
        obtain ⟨_, _, h⟩ := (mem_mggF2OutNeighbors_iff hm0 S q.1 q.2).mp (mem_filter.mp hw).1
        exact h
      obtain ⟨s, hs, t, ht, hst, hsw, htw⟩ : ∃ s ∈ mggF2VertGens, ∃ t ∈ mggF2VertGens,
          s ≠ t ∧ mggF2Neighbor hm0 q.1 s = q.2 ∧ mggF2Neighbor hm0 q.1 t = q.2 := by
        rcases hcase with ⟨hy, _⟩ | ⟨_, h⟩
        · exact absurd (by
            rw [← mggEncode_decode hm0 q.2, ← mggEncode_decode hm0 q.1, Prod.ext hqx hy])
            hne
        · exact h
      refine (mem_mggF2Pairs_iff _ _ _).mpr ⟨?_, ?_⟩
      · exact mggF2_mem_doubledOffsets_of_vert hm0 hne hs ht hst hsw htw
      · refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
        · rw [show ((mggDecode hm0 q.1).1, (mggDecode hm0 q.1).2) = mggDecode hm0 q.1 from
            rfl, mggEncode_decode]
          exact hv
        · rw [add_sub_cancel, ← hqx,
            show ((mggDecode hm0 q.2).1, (mggDecode hm0 q.2).2) = mggDecode hm0 q.2 from rfl,
            mggEncode_decode]
          exact hwn
    · intro q hq q' hq' h
      obtain ⟨_, hqx⟩ := mem_filter.mp hq
      obtain ⟨_, hqx'⟩ := mem_filter.mp hq'
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨hx, hδ⟩, hy⟩ := h
      have hv : q.1 = q'.1 := by
        rw [← mggEncode_decode hm0 q.1, ← mggEncode_decode hm0 q'.1, Prod.ext hx hy]
      have hyw : (mggDecode hm0 q.2).2 = (mggDecode hm0 q'.2).2 := by
        have := congrArg (fun z => z + (mggDecode hm0 q.1).2) hδ
        simpa [sub_add_cancel, hy] using this
      have hxw : (mggDecode hm0 q.2).1 = (mggDecode hm0 q'.2).1 := by
        rw [hqx, hqx', hx]
      have hw : q.2 = q'.2 := by
        rw [← mggEncode_decode hm0 q.2, ← mggEncode_decode hm0 q'.2, Prod.ext hxw hyw]
      exact Prod.ext hv hw
  omega

/-- At most `2m` doubled cut pairs: every doubled pair is horizontal or vertical. -/
theorem mggF2DoubledCutPairs_card_le_two_mul {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    (mggF2DoubledCutPairs (lt_of_lt_of_le (by decide : 0 < 2) hm) S).card ≤ 2 * m := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  letI : NeZero m := ⟨ne_of_gt hm0⟩
  have hH := mggF2_horiz_doubledCutPairs_card_le hm S
  have hV := mggF2_vert_doubledCutPairs_card_le hm S
  have hsub : mggF2DoubledCutPairs hm0 S ⊆
      ((mggF2DoubledCutPairs hm0 S).filter fun q =>
          (mggDecode hm0 q.2).2 = (mggDecode hm0 q.1).2) ∪
        ((mggF2DoubledCutPairs hm0 S).filter fun q =>
          (mggDecode hm0 q.2).1 = (mggDecode hm0 q.1).1) := by
    intro q hq
    obtain ⟨hv, hw⟩ := (mem_mggF2Pairs_iff _ _ q).mp hq
    obtain ⟨_, hcase⟩ := mggF2_dblOut_horiz_or_vert hm0 S hv hw
    rcases hcase with ⟨hy, _⟩ | ⟨hx, _⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, hy⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hq, hx⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  omega

/-- Reverse cut loss through doubled targets is at most `2m`. -/
theorem mggF2_sum_dblOut_card_le_two_mul {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    (∑ v ∈ S, (mggF2DblOut (lt_of_lt_of_le (by decide : 0 < 2) hm) S v).card) ≤ 2 * m := by
  rw [← mggF2DoubledCutPairs_card]
  exact mggF2DoubledCutPairs_card_le_two_mul hm S

/-- Additive multiplicity budget: `multiCut ≤ |∂S| + 2m`. Independent of the unit-shear
loss lemmas and of `mggF2MultiCutCard_le_two_mul_edgeBoundary`. -/
theorem mggF2MultiCutCard_le_edgeBoundary_add_two_mul {m : ℕ} (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 2) hm) S ≤
      (edgeBoundary (mggF2Graph m (lt_of_lt_of_le (by decide : 0 < 2) hm)) S).card +
        2 * m := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have h1 := mggF2MultiCutCard_le_sum_out_add_dblOut hm0 S
  have h2 := sum_mggF2OutNeighbors_card_le_edgeBoundary hm0 S
  have h3 := mggF2_sum_dblOut_card_le_two_mul hm S
  omega

end SATurday.ProofComplexity
