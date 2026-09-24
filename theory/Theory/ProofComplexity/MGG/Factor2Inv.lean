import Theory.ProofComplexity.MGG.Factor2Spectral
import Mathlib.Tactic

/-!
# Factor-2 multi-to-simple loss and Inv packaging (R2 Block A checklist item 3)

Fresh reverse-cut loss for `mggF2Neighbor`, independent of every unit-shear loss
lemma (`mggLeavingExcess_le_four`, `mggReverseCutLoss_le_four_mul_edgeBoundary`,
`mggReverseCutLoss_le_two_mul_card_add_twelve_mul_m`) and of the Inv-15 packaging
`mggGraph_hasExpansionInv15_of_multi_cheeger`.

Content, in dependency order.

1. `mggF2OutNeighbors`, `mggF2LeavingExcess`, `mggF2ReverseCutLoss` with the
   splitting identity `multiCut = sum out-degrees + reverseLoss`.
2. Non-loop neighbor fibers have size at most two: horizontal generators keep the
   `y` coordinate, vertical generators keep `x`, so a non-loop target is hit by
   one family only; inside a family the two offsets `2y` and `2y + 1` differ, and
   so do `-(2y)` and `-(2y + 1)`, leaving at most one hit per signed pair.
3. Hence `|leavingGens v| <= 2 * |outNeighbors v|` for `v` in `S`, so
   `reverseLoss <= sum out-degrees`.
4. Distinct out-neighbors inject into the simple cut (directed cut pairs), giving
   `sum out-degrees <= |edgeBoundary|` and `multiCut <= 2 * |edgeBoundary|`.
5. Packaging. Multi Cheeger `2|S| <= 5 * multiCut` plus `multiCut <= 2|∂|` is
   exactly `HasExpansionInv _ 5` (`mggF2Graph_hasExpansionInv5`, unconditional).
   Locked `mggInvK = 4` needs more. Sets of density at most `461 / 1000` are
   certified outright by `mggF2_card_le_four_mul_edgeBoundary_of_sparse`, which
   keeps the mass factor `(m² - |S|) / m²` of `mggF2MultiCut_ge_gap_mass` instead
   of discarding it at one half. The dense band and the locked Inv-4 packaging
   live in `MGG.Factor2Inv4` (additive loss plus line dichotomy; no twelfth
   witness and no unit-shear Inv-15). Small sets ride on positivity of the cut,
   which follows from `mggF2Graph_isConnected`.

LOG: R2 Block A factor-2 reverse loss, multiCut <= 2 cut, Inv-5 certified, sparse Inv-4
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Out-neighbors, leaving excess, reverse cut loss -/

/-- Distinct outside neighbors of `v` under the eight factor-2 generators. -/
def mggF2OutNeighbors {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : Finset (Fin (m * m)) :=
  (mggF2LeavingGens hm S v).image fun s => mggF2Neighbor hm v s

theorem mem_mggF2OutNeighbors_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m)) :
    w ∈ mggF2OutNeighbors hm S v ↔
      ∃ s : Fin 8, mggF2Neighbor hm v s = w ∧ w ∉ S := by
  constructor
  · intro hw
    obtain ⟨s, hsL, rfl⟩ := mem_image.mp hw
    exact ⟨s, rfl, (mem_mggF2LeavingGens_iff hm S v s).mp hsL⟩
  · rintro ⟨s, rfl, hsn⟩
    exact mem_image.mpr ⟨s, (mem_mggF2LeavingGens_iff hm S v s).mpr hsn, rfl⟩

theorem mggF2OutNeighbors_card_le_leavingGens {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    (mggF2OutNeighbors hm S v).card ≤ (mggF2LeavingGens hm S v).card :=
  card_image_le

/-- Parallel leaving excess at `v`: labels beyond the distinct-target count. -/
def mggF2LeavingExcess {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) : ℕ :=
  (mggF2LeavingGens hm S v).card - (mggF2OutNeighbors hm S v).card

theorem mggF2LeavingGens_card_eq_out_add_excess {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) :
    (mggF2LeavingGens hm S v).card =
      (mggF2OutNeighbors hm S v).card + mggF2LeavingExcess hm S v := by
  simp only [mggF2LeavingExcess]
  rw [add_comm]
  exact (Nat.sub_add_cancel (mggF2OutNeighbors_card_le_leavingGens hm S v)).symm

/-- Total reverse cut loss over `S`. -/
def mggF2ReverseCutLoss {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) : ℕ :=
  ∑ v ∈ S, mggF2LeavingExcess hm S v

theorem mggF2MultiCutCard_eq_sum_out_add_reverseLoss {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiCutCard hm S =
      (∑ v ∈ S, (mggF2OutNeighbors hm S v).card) + mggF2ReverseCutLoss hm S := by
  classical
  calc
    mggF2MultiCutCard hm S = ∑ v ∈ S, (mggF2LeavingGens hm S v).card :=
      (mggF2LeavingGens_card_sum hm S).symm
    _ = ∑ v ∈ S,
          ((mggF2OutNeighbors hm S v).card + mggF2LeavingExcess hm S v) :=
      sum_congr rfl fun v _ => mggF2LeavingGens_card_eq_out_add_excess hm S v
    _ = (∑ v ∈ S, (mggF2OutNeighbors hm S v).card) +
          ∑ v ∈ S, mggF2LeavingExcess hm S v := sum_add_distrib
    _ = (∑ v ∈ S, (mggF2OutNeighbors hm S v).card) + mggF2ReverseCutLoss hm S :=
      rfl

/-! ## Horizontal and vertical generator families

Horizontal generators shift `x` and keep `y`; vertical generators shift `y` and
keep `x`. The pair order `{+, +succ, -, -succ}` is the one the fiber lemma needs.
-/

/-- The four generators that move only the `x` coordinate. -/
def mggF2HorizGens : Finset (Fin 8) :=
  {mggF2Xp2y, mggF2Xp2y1, mggF2Xm2y, mggF2Xm2y1}

/-- The four generators that move only the `y` coordinate. -/
def mggF2VertGens : Finset (Fin 8) :=
  {mggF2Yp2x, mggF2Yp2x1, mggF2Ym2x, mggF2Ym2x1}

theorem mggF2HorizGens_card : mggF2HorizGens.card = 4 := by decide

theorem mggF2VertGens_card : mggF2VertGens.card = 4 := by decide

theorem mggF2HorizGens_disjoint_vert : Disjoint mggF2HorizGens mggF2VertGens := by
  decide

theorem mggF2HorizGens_union_vert :
    mggF2HorizGens ∪ mggF2VertGens = (univ : Finset (Fin 8)) := by decide

theorem mem_mggF2HorizGens_iff (s : Fin 8) :
    s ∈ mggF2HorizGens ↔
      s = mggF2Xp2y ∨ s = mggF2Xp2y1 ∨ s = mggF2Xm2y ∨ s = mggF2Xm2y1 := by
  fin_cases s <;> decide

theorem mem_mggF2VertGens_iff (s : Fin 8) :
    s ∈ mggF2VertGens ↔
      s = mggF2Yp2x ∨ s = mggF2Yp2x1 ∨ s = mggF2Ym2x ∨ s = mggF2Ym2x1 := by
  fin_cases s <;> decide

/-- Every label is horizontal or vertical. -/
theorem mem_mggF2HorizGens_or_vert (s : Fin 8) :
    s ∈ mggF2HorizGens ∨ s ∈ mggF2VertGens := by
  have h : s ∈ mggF2HorizGens ∪ mggF2VertGens := by
    rw [mggF2HorizGens_union_vert]; exact mem_univ s
  exact mem_union.mp h

theorem mggF2Neighbor_horiz_same_y {m : ℕ} (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggF2HorizGens) :
    (mggDecode hm (mggF2Neighbor hm v s)).2 = (mggDecode hm v).2 := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rcases (mem_mggF2HorizGens_iff s).mp hs with rfl | rfl | rfl | rfl
  · simp [mggF2Neighbor_Xp2y_eq, mggDecode_encode]
  · simp [mggF2Neighbor_Xp2y1_eq, mggDecode_encode]
  · simp [mggF2Neighbor_Xm2y_eq, mggDecode_encode]
  · simp [mggF2Neighbor_Xm2y1_eq, mggDecode_encode]

theorem mggF2Neighbor_vert_same_x {m : ℕ} (hm : 0 < m) (v : Fin (m * m))
    {s : Fin 8} (hs : s ∈ mggF2VertGens) :
    (mggDecode hm (mggF2Neighbor hm v s)).1 = (mggDecode hm v).1 := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rcases (mem_mggF2VertGens_iff s).mp hs with rfl | rfl | rfl | rfl
  · simp [mggF2Neighbor_Yp2x_eq, mggDecode_encode]
  · simp [mggF2Neighbor_Yp2x1_eq, mggDecode_encode]
  · simp [mggF2Neighbor_Ym2x_eq, mggDecode_encode]
  · simp [mggF2Neighbor_Ym2x1_eq, mggDecode_encode]

/-- A non-loop horizontal target is never a vertical target: a common value would
agree with `v` in both coordinates. -/
theorem mggF2Neighbor_horiz_ne_vert_of_ne_self {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) {s t : Fin 8}
    (hs : s ∈ mggF2HorizGens) (ht : t ∈ mggF2VertGens)
    (hne : mggF2Neighbor hm v s ≠ v) :
    mggF2Neighbor hm v s ≠ mggF2Neighbor hm v t := by
  intro heq
  have hy : (mggDecode hm (mggF2Neighbor hm v s)).2 = (mggDecode hm v).2 :=
    mggF2Neighbor_horiz_same_y hm v hs
  have hx : (mggDecode hm (mggF2Neighbor hm v s)).1 = (mggDecode hm v).1 := by
    rw [heq]
    exact mggF2Neighbor_vert_same_x hm v ht
  have hdec : mggDecode hm (mggF2Neighbor hm v s) = mggDecode hm v :=
    Prod.ext hx hy
  refine hne ?_
  calc
    mggF2Neighbor hm v s
        = mggEncode hm (mggDecode hm (mggF2Neighbor hm v s)) :=
          (mggEncode_decode hm _).symm
    _ = mggEncode hm (mggDecode hm v) := by rw [hdec]
    _ = v := mggEncode_decode hm v

/-! ## Non-loop fibers have size at most two -/

/-- Generic counting step: inside a four-element index set split into two pairs,
each pair contributing at most one hit, a fiber has at most two elements. -/
private theorem mggF2_pair_fiber_card_le_two {α β : Type*} [DecidableEq α]
    [DecidableEq β] {a b c d : α} {f : α → β} {δ : β}
    (hab : f a ≠ f b) (hcd : f c ≠ f d) :
    (({a, b, c, d} : Finset α).filter fun s => f s = δ).card ≤ 2 := by
  classical
  set F := ({a, b, c, d} : Finset α).filter fun s => f s = δ with hF
  have hone : ∀ u w : α, f u ≠ f w → (F ∩ ({u, w} : Finset α)).card ≤ 1 := by
    intro u w huw
    rw [Finset.card_le_one]
    intro p hp q hq
    have hpF := (mem_inter.mp hp).1
    have hqF := (mem_inter.mp hq).1
    have hpP := (mem_inter.mp hp).2
    have hqP := (mem_inter.mp hq).2
    have hpf : f p = δ := (mem_filter.mp hpF).2
    have hqf : f q = δ := (mem_filter.mp hqF).2
    simp only [mem_insert, mem_singleton] at hpP hqP
    rcases hpP with rfl | rfl <;> rcases hqP with rfl | rfl
    · rfl
    · exact absurd (hpf.trans hqf.symm) huw
    · exact absurd (hqf.trans hpf.symm) huw
    · rfl
  have hsub : F ⊆ (F ∩ ({a, b} : Finset α)) ∪ (F ∩ ({c, d} : Finset α)) := by
    intro s hs
    have hmem : s ∈ ({a, b, c, d} : Finset α) := (mem_filter.mp hs).1
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact mem_union_left _ (mem_inter.mpr ⟨hs, by simp⟩)
    · exact mem_union_left _ (mem_inter.mpr ⟨hs, by simp⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hs, by simp⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hs, by simp⟩)
  have hle := (card_le_card hsub).trans (card_union_le _ _)
  have h1 := hone a b hab
  have h2 := hone c d hcd
  omega

/-- `+(2y)` and `+(2y+1)` land on different vertices when `1 < m`. -/
theorem mggF2Neighbor_Xp2y_ne_Xp2y1 {m : ℕ} (hm : 0 < m) (hm1 : 1 < m)
    (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Xp2y ≠ mggF2Neighbor hm v mggF2Xp2y1 := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  intro h
  rw [mggF2Neighbor_Xp2y_eq, mggF2Neighbor_Xp2y1_eq] at h
  have hdec := congrArg (mggDecode hm) h
  rw [mggDecode_encode, mggDecode_encode] at hdec
  have hx := (Prod.ext_iff.mp hdec).1
  exact Fin.add_one_ne_of_one_lt hm1 _ hx.symm

/-- `-(2y)` and `-(2y+1)` land on different vertices when `1 < m`. -/
theorem mggF2Neighbor_Xm2y_ne_Xm2y1 {m : ℕ} (hm : 0 < m) (hm1 : 1 < m)
    (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Xm2y ≠ mggF2Neighbor hm v mggF2Xm2y1 := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  intro h
  rw [mggF2Neighbor_Xm2y_eq, mggF2Neighbor_Xm2y1_eq] at h
  have hdec := congrArg (mggDecode hm) h
  rw [mggDecode_encode, mggDecode_encode] at hdec
  have hx := (Prod.ext_iff.mp hdec).1
  have hx' : (mggDecode hm v).1 - (mggDecode hm v).2 - (mggDecode hm v).2 - 1 + 1 =
      (mggDecode hm v).1 - (mggDecode hm v).2 - (mggDecode hm v).2 := by
    rw [sub_add_cancel]
  exact Fin.add_one_ne_of_one_lt hm1 _ (hx'.trans hx)

/-- `+(2x)` and `+(2x+1)` land on different vertices when `1 < m`. -/
theorem mggF2Neighbor_Yp2x_ne_Yp2x1 {m : ℕ} (hm : 0 < m) (hm1 : 1 < m)
    (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Yp2x ≠ mggF2Neighbor hm v mggF2Yp2x1 := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  intro h
  rw [mggF2Neighbor_Yp2x_eq, mggF2Neighbor_Yp2x1_eq] at h
  have hdec := congrArg (mggDecode hm) h
  rw [mggDecode_encode, mggDecode_encode] at hdec
  have hy := (Prod.ext_iff.mp hdec).2
  exact Fin.add_one_ne_of_one_lt hm1 _ hy.symm

/-- `-(2x)` and `-(2x+1)` land on different vertices when `1 < m`. -/
theorem mggF2Neighbor_Ym2x_ne_Ym2x1 {m : ℕ} (hm : 0 < m) (hm1 : 1 < m)
    (v : Fin (m * m)) :
    mggF2Neighbor hm v mggF2Ym2x ≠ mggF2Neighbor hm v mggF2Ym2x1 := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  intro h
  rw [mggF2Neighbor_Ym2x_eq, mggF2Neighbor_Ym2x1_eq] at h
  have hdec := congrArg (mggDecode hm) h
  rw [mggDecode_encode, mggDecode_encode] at hdec
  have hy := (Prod.ext_iff.mp hdec).2
  have hy' : (mggDecode hm v).2 - (mggDecode hm v).1 - (mggDecode hm v).1 - 1 + 1 =
      (mggDecode hm v).2 - (mggDecode hm v).1 - (mggDecode hm v).1 := by
    rw [sub_add_cancel]
  exact Fin.add_one_ne_of_one_lt hm1 _ (hy'.trans hy)

theorem mggF2_horiz_fiber_card_le_two {m : ℕ} (hm : 0 < m) (hm1 : 1 < m)
    (v w : Fin (m * m)) :
    (mggF2HorizGens.filter fun s => mggF2Neighbor hm v s = w).card ≤ 2 := by
  unfold mggF2HorizGens
  exact mggF2_pair_fiber_card_le_two (mggF2Neighbor_Xp2y_ne_Xp2y1 hm hm1 v)
    (mggF2Neighbor_Xm2y_ne_Xm2y1 hm hm1 v)

theorem mggF2_vert_fiber_card_le_two {m : ℕ} (hm : 0 < m) (hm1 : 1 < m)
    (v w : Fin (m * m)) :
    (mggF2VertGens.filter fun s => mggF2Neighbor hm v s = w).card ≤ 2 := by
  unfold mggF2VertGens
  exact mggF2_pair_fiber_card_le_two (mggF2Neighbor_Yp2x_ne_Yp2x1 hm hm1 v)
    (mggF2Neighbor_Ym2x_ne_Ym2x1 hm hm1 v)

/-- Two distinct vertices force `1 < m`. -/
private theorem mggF2_one_lt_of_ne {m : ℕ} (hm : 0 < m) {v w : Fin (m * m)}
    (hne : w ≠ v) : 1 < m := by
  have hvw : w.val ≠ v.val := fun h => hne (Fin.ext h)
  have hv := v.isLt
  have hw := w.isLt
  have hmm : 1 < m * m := by omega
  by_contra hc
  have hm1 : m = 1 := by omega
  subst hm1
  simp at hmm

/-- At most two of the eight labels reach a target other than `v` itself. -/
theorem mggF2_labels_to_ne_neighbor_card_le_two {m : ℕ} (hm : 0 < m)
    (v w : Fin (m * m)) (hne : w ≠ v) :
    ((univ : Finset (Fin 8)).filter fun s => mggF2Neighbor hm v s = w).card ≤ 2 := by
  classical
  have hm1 : 1 < m := mggF2_one_lt_of_ne hm hne
  set L := (univ : Finset (Fin 8)).filter fun s => mggF2Neighbor hm v s = w with hL
  by_cases hH : ∃ s ∈ L, s ∈ mggF2HorizGens
  · obtain ⟨s, hsL, hsH⟩ := hH
    have hsw : mggF2Neighbor hm v s = w := (mem_filter.mp hsL).2
    have hsne : mggF2Neighbor hm v s ≠ v := by rw [hsw]; exact hne
    have hsub : L ⊆ mggF2HorizGens.filter fun t => mggF2Neighbor hm v t = w := by
      intro t htL
      have htw : mggF2Neighbor hm v t = w := (mem_filter.mp htL).2
      refine mem_filter.mpr ⟨?_, htw⟩
      rcases mem_mggF2HorizGens_or_vert t with htH | htV
      · exact htH
      · exact absurd (by rw [hsw, htw])
          (mggF2Neighbor_horiz_ne_vert_of_ne_self hm v hsH htV hsne)
    exact (card_le_card hsub).trans (mggF2_horiz_fiber_card_le_two hm hm1 v w)
  · have hH' : ∀ t ∈ L, t ∉ mggF2HorizGens := fun t htL htH => hH ⟨t, htL, htH⟩
    have hsub : L ⊆ mggF2VertGens.filter fun t => mggF2Neighbor hm v t = w := by
      intro t htL
      have htw : mggF2Neighbor hm v t = w := (mem_filter.mp htL).2
      refine mem_filter.mpr ⟨?_, htw⟩
      rcases mem_mggF2HorizGens_or_vert t with htH | htV
      · exact absurd htH (hH' t htL)
      · exact htV
    exact (card_le_card hsub).trans (mggF2_vert_fiber_card_le_two hm hm1 v w)

/-! ## Leaving labels are at most twice the out-degree -/

theorem mggF2Neighbor_ne_of_mem_not_mem {m : ℕ} {S : Finset (Fin (m * m))}
    {v w : Fin (m * m)} (hv : v ∈ S) (hw : w ∉ S) : w ≠ v :=
  fun h => hw (h ▸ hv)

theorem mggF2LeavingGens_card_le_two_mul_outNeighbors_of_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S) :
    (mggF2LeavingGens hm S v).card ≤ 2 * (mggF2OutNeighbors hm S v).card := by
  classical
  have hsum :
      (mggF2LeavingGens hm S v).card =
        ∑ w ∈ mggF2OutNeighbors hm S v,
          ((mggF2LeavingGens hm S v).filter fun s =>
            mggF2Neighbor hm v s = w).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro s hs
    simp only [mggF2OutNeighbors]
    exact mem_image.mpr ⟨s, hs, rfl⟩
  have hle :
      ∑ w ∈ mggF2OutNeighbors hm S v,
          ((mggF2LeavingGens hm S v).filter fun s =>
            mggF2Neighbor hm v s = w).card ≤
        ∑ _w ∈ mggF2OutNeighbors hm S v, 2 := by
    refine sum_le_sum fun w hw => ?_
    obtain ⟨_, _, hwn⟩ := (mem_mggF2OutNeighbors_iff hm S v w).mp hw
    have hne : w ≠ v := mggF2Neighbor_ne_of_mem_not_mem hv hwn
    have hsub :
        (mggF2LeavingGens hm S v).filter (fun s => mggF2Neighbor hm v s = w) ⊆
          (univ : Finset (Fin 8)).filter fun s => mggF2Neighbor hm v s = w :=
      filter_subset_filter _ (subset_univ _)
    exact (card_le_card hsub).trans
      (mggF2_labels_to_ne_neighbor_card_le_two hm v w hne)
  have hconst : (∑ _w ∈ mggF2OutNeighbors hm S v, (2 : ℕ)) =
      2 * (mggF2OutNeighbors hm S v).card := by
    simp [sum_const, Nat.mul_comm]
  exact (le_of_eq hsum).trans (hle.trans (le_of_eq hconst))

theorem mggF2LeavingExcess_le_outNeighbors_of_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S) :
    mggF2LeavingExcess hm S v ≤ (mggF2OutNeighbors hm S v).card := by
  have h := mggF2LeavingGens_card_le_two_mul_outNeighbors_of_mem hm S v hv
  have heq := mggF2LeavingGens_card_eq_out_add_excess hm S v
  omega

theorem mggF2ReverseCutLoss_le_sum_outNeighbors {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2ReverseCutLoss hm S ≤ ∑ v ∈ S, (mggF2OutNeighbors hm S v).card :=
  sum_le_sum fun v hv => mggF2LeavingExcess_le_outNeighbors_of_mem hm S v hv

/-! ## Distinct out-neighbors inject into the simple cut -/

/-- Endpoints of a realized `mggF2EdgeOf` are `v` and its neighbor. -/
theorem mggF2EdgeOf_eq_some_endpoints {m : ℕ} (hm : 0 < m)
    (v : Fin (m * m)) (s : Fin 8) {e : FinEdge (m * m)}
    (he : mggF2EdgeOf hm v s = some e) :
    (e.val.1 = v ∧ e.val.2 = mggF2Neighbor hm v s) ∨
      (e.val.1 = mggF2Neighbor hm v s ∧ e.val.2 = v) := by
  have hne : mggF2Neighbor hm v s ≠ v := by
    intro hloop
    simp [mggF2EdgeOf, hloop] at he
  obtain ⟨e', he', hends⟩ := mggF2EdgeOf_eq_some_of_ne hm v s hne
  have hee : e' = e := by
    rw [he'] at he
    exact Option.some_injective _ he
  subst hee
  exact hends

/-- A leaving label at a vertex of `S` produces a concrete cut edge. -/
theorem mggF2EdgeOf_eq_some_mem_edgeBoundary_of_leaving {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S) (s : Fin 8)
    (hw : mggF2Neighbor hm v s ∉ S) :
    ∃ e, mggF2EdgeOf hm v s = some e ∧ e ∈ edgeBoundary (mggF2Graph m hm) S := by
  have hne : mggF2Neighbor hm v s ≠ v :=
    mggF2Neighbor_ne_of_mem_not_mem hv hw
  obtain ⟨e, he, hends⟩ := mggF2EdgeOf_eq_some_of_ne hm v s hne
  refine ⟨e, he, ?_⟩
  refine (mem_edgeBoundary_iff).mpr ⟨mem_mggF2Graph_of_edgeOf hm v s he, ?_⟩
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1 ▸ hv, h2 ▸ hw⟩
  · exact Or.inr ⟨h1 ▸ hw, h2 ▸ hv⟩

/-- Witness generator for an out-neighbor. -/
noncomputable def mggF2OutNeighborWitness {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m))
    (hw : w ∈ mggF2OutNeighbors hm S v) : Fin 8 :=
  Classical.choose ((mem_mggF2OutNeighbors_iff hm S v w).mp hw)

theorem mggF2OutNeighborWitness_eq {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m))
    (hw : w ∈ mggF2OutNeighbors hm S v) :
    mggF2Neighbor hm v (mggF2OutNeighborWitness hm S v w hw) = w :=
  (Classical.choose_spec ((mem_mggF2OutNeighbors_iff hm S v w).mp hw)).1

theorem mggF2OutNeighborWitness_not_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v w : Fin (m * m))
    (hw : w ∈ mggF2OutNeighbors hm S v) : w ∉ S :=
  (Classical.choose_spec ((mem_mggF2OutNeighbors_iff hm S v w).mp hw)).2

theorem mggF2EdgeOf_outNeighbor_mem_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggF2OutNeighbors hm S v) :
    ∃ e, mggF2EdgeOf hm v (mggF2OutNeighborWitness hm S v w hw) = some e ∧
      e ∈ edgeBoundary (mggF2Graph m hm) S :=
  mggF2EdgeOf_eq_some_mem_edgeBoundary_of_leaving hm S v hv
    (mggF2OutNeighborWitness hm S v w hw)
    (by
      rw [mggF2OutNeighborWitness_eq hm S v w hw]
      exact mggF2OutNeighborWitness_not_mem hm S v w hw)

/-- The simple cut edge realizing the directed pair `(v, w)`. -/
noncomputable def mggF2OutEdge {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggF2OutNeighbors hm S v) : FinEdge (m * m) :=
  Classical.choose (mggF2EdgeOf_outNeighbor_mem_edgeBoundary hm S v hv w hw)

theorem mggF2OutEdge_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggF2OutNeighbors hm S v) :
    mggF2OutEdge hm S v hv w hw ∈ edgeBoundary (mggF2Graph m hm) S :=
  (Classical.choose_spec
    (mggF2EdgeOf_outNeighbor_mem_edgeBoundary hm S v hv w hw)).2

theorem mggF2OutEdge_eq_some {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggF2OutNeighbors hm S v) :
    mggF2EdgeOf hm v (mggF2OutNeighborWitness hm S v w hw) =
      some (mggF2OutEdge hm S v hv w hw) :=
  (Classical.choose_spec
    (mggF2EdgeOf_outNeighbor_mem_edgeBoundary hm S v hv w hw)).1

theorem mggF2OutEdge_endpoints {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (v : Fin (m * m)) (hv : v ∈ S)
    (w : Fin (m * m)) (hw : w ∈ mggF2OutNeighbors hm S v) :
    ((mggF2OutEdge hm S v hv w hw).val.1 = v ∧
        (mggF2OutEdge hm S v hv w hw).val.2 = w) ∨
      ((mggF2OutEdge hm S v hv w hw).val.1 = w ∧
        (mggF2OutEdge hm S v hv w hw).val.2 = v) := by
  have he := mggF2OutEdge_eq_some hm S v hv w hw
  have hnw := mggF2OutNeighborWitness_eq hm S v w hw
  have hends := mggF2EdgeOf_eq_some_endpoints hm v
    (mggF2OutNeighborWitness hm S v w hw) he
  simpa [hnw] using hends

/-- Directed cut pairs `(v, w)` with `v ∈ S` and `w` a distinct out-neighbor. -/
def mggF2DirectedCutPairs {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin (m * m) × Fin (m * m)) :=
  S.biUnion fun v => (mggF2OutNeighbors hm S v).image fun w => (v, w)

theorem mem_mggF2DirectedCutPairs_iff {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin (m * m) × Fin (m * m)) :
    p ∈ mggF2DirectedCutPairs hm S ↔
      p.1 ∈ S ∧ p.2 ∈ mggF2OutNeighbors hm S p.1 := by
  simp only [mggF2DirectedCutPairs, mem_biUnion, mem_image]
  constructor
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨hv, hw⟩
  · rintro ⟨hv, hw⟩
    exact ⟨p.1, hv, p.2, hw, rfl⟩

theorem mggF2DirectedCutPairs_card {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (mggF2DirectedCutPairs hm S).card =
      ∑ v ∈ S, (mggF2OutNeighbors hm S v).card := by
  classical
  have hdisj :
      (S : Set (Fin (m * m))).PairwiseDisjoint fun v =>
        (mggF2OutNeighbors hm S v).image fun w => (v, w) := by
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
  rw [mggF2DirectedCutPairs, card_biUnion hdisj]
  exact sum_congr rfl fun v _ =>
    card_image_of_injective _ fun _ _ h => (Prod.ext_iff.mp h).2

noncomputable def mggF2DirectedCutEdge {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (p : Fin (m * m) × Fin (m * m))
    (hp : p ∈ mggF2DirectedCutPairs hm S) : FinEdge (m * m) :=
  mggF2OutEdge hm S p.1 ((mem_mggF2DirectedCutPairs_iff hm S p).mp hp).1
    p.2 ((mem_mggF2DirectedCutPairs_iff hm S p).mp hp).2

theorem mggF2DirectedCutEdge_mem {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) {p : Fin (m * m) × Fin (m * m)}
    (hp : p ∈ mggF2DirectedCutPairs hm S) :
    mggF2DirectedCutEdge hm S p hp ∈ edgeBoundary (mggF2Graph m hm) S := by
  simpa [mggF2DirectedCutEdge] using
    mggF2OutEdge_mem hm S p.1 ((mem_mggF2DirectedCutPairs_iff hm S p).mp hp).1
      p.2 ((mem_mggF2DirectedCutPairs_iff hm S p).mp hp).2

theorem mggF2DirectedCutEdge_injective {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m)))
    {p₁ : Fin (m * m) × Fin (m * m)} (hp₁ : p₁ ∈ mggF2DirectedCutPairs hm S)
    {p₂ : Fin (m * m) × Fin (m * m)} (hp₂ : p₂ ∈ mggF2DirectedCutPairs hm S)
    (h : mggF2DirectedCutEdge hm S p₁ hp₁ = mggF2DirectedCutEdge hm S p₂ hp₂) :
    p₁ = p₂ := by
  have hv₁ := ((mem_mggF2DirectedCutPairs_iff hm S p₁).mp hp₁).1
  have hw₁ := ((mem_mggF2DirectedCutPairs_iff hm S p₁).mp hp₁).2
  have hv₂ := ((mem_mggF2DirectedCutPairs_iff hm S p₂).mp hp₂).1
  have hw₂ := ((mem_mggF2DirectedCutPairs_iff hm S p₂).mp hp₂).2
  have hw₁n := mggF2OutNeighborWitness_not_mem hm S p₁.1 p₁.2 hw₁
  have hw₂n := mggF2OutNeighborWitness_not_mem hm S p₂.1 p₂.2 hw₂
  have e1 := mggF2OutEdge_endpoints hm S p₁.1 hv₁ p₁.2 hw₁
  have e2 := mggF2OutEdge_endpoints hm S p₂.1 hv₂ p₂.2 hw₂
  have heq :
      (mggF2OutEdge hm S p₁.1 hv₁ p₁.2 hw₁).val =
        (mggF2OutEdge hm S p₂.1 hv₂ p₂.2 hw₂).val :=
    congrArg Subtype.val (by simpa [mggF2DirectedCutEdge] using h)
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
theorem sum_mggF2OutNeighbors_card_le_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (∑ v ∈ S, (mggF2OutNeighbors hm S v).card) ≤
      (edgeBoundary (mggF2Graph m hm) S).card := by
  classical
  rw [← mggF2DirectedCutPairs_card hm S]
  have h :=
    card_le_card_of_injOn
      (s := (mggF2DirectedCutPairs hm S).attach)
      (t := edgeBoundary (mggF2Graph m hm) S)
      (fun p => mggF2DirectedCutEdge hm S p.1 p.2)
      (fun p _ => mggF2DirectedCutEdge_mem hm S p.2)
      (fun p₁ _ p₂ _ h =>
        Subtype.ext (mggF2DirectedCutEdge_injective hm S p₁.2 p₂.2 h))
  simpa [card_attach] using h

/-- Reverse cut loss is at most the simple cut. -/
theorem mggF2ReverseCutLoss_le_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2ReverseCutLoss hm S ≤ (edgeBoundary (mggF2Graph m hm) S).card :=
  (mggF2ReverseCutLoss_le_sum_outNeighbors hm S).trans
    (sum_mggF2OutNeighbors_card_le_edgeBoundary hm S)

/-- Multi-cut is at most twice the simple cut: every non-loop fiber has size at
most two, so the labeled cut over-counts each simple cut edge at most twice. -/
theorem mggF2MultiCutCard_le_two_mul_edgeBoundary {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiCutCard hm S ≤ 2 * (edgeBoundary (mggF2Graph m hm) S).card := by
  have hsplit := mggF2MultiCutCard_eq_sum_out_add_reverseLoss hm S
  have hloss := mggF2ReverseCutLoss_le_sum_outNeighbors hm S
  have hinj := sum_mggF2OutNeighbors_card_le_edgeBoundary hm S
  omega

/-! ## Connectivity gives a nonempty cut for nonempty half-sets -/

/-- A nonempty half-set in the connected factor-2 graph has at least one cut
edge. Uses `mggF2Graph_isConnected`, never `mggGraph_isConnected`. -/
theorem mggF2_edgeBoundary_card_pos {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin (m * m))) (hne : S.Nonempty)
    (hhalf : 2 * S.card ≤ m * m) :
    0 < (edgeBoundary (mggF2Graph m hm) S).card := by
  classical
  refine Nat.pos_of_ne_zero ?_
  intro hzero
  have hempty : edgeBoundary (mggF2Graph m hm) S = ∅ := card_eq_zero.mp hzero
  have hstay : ∀ {a b : Fin (m * m)},
      (mggF2Graph m hm).Adj a b → a ∈ S → b ∈ S := by
    intro a b hadj ha
    by_contra hb
    obtain ⟨e, heG, hends⟩ := hadj
    have hcut : e ∈ edgeBoundary (mggF2Graph m hm) S := by
      refine (mem_edgeBoundary_iff).mpr ⟨heG, ?_⟩
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1]; exact ha, by rw [h2]; exact hb⟩
      · exact Or.inr ⟨by rw [h1]; exact hb, by rw [h2]; exact ha⟩
    rw [hempty] at hcut
    exact absurd hcut (notMem_empty e)
  obtain ⟨v, hv⟩ := hne
  have hcl : ∀ u : Fin (m * m), (mggF2Graph m hm).Reachable v u → u ∈ S := by
    intro u hu
    induction hu with
    | refl => exact hv
    | tail _ hadj ih => exact hstay hadj ih
  have hall : ∀ u : Fin (m * m), u ∈ S := fun u =>
    hcl u (mggF2Graph_isConnected hm v u)
  have hSu : S = (univ : Finset (Fin (m * m))) := eq_univ_iff_forall.mpr hall
  have hcard : S.card = m * m := by
    rw [hSu, card_univ, Fintype.card_fin]
  have hmpos : 0 < m * m := Nat.mul_pos hm hm
  omega

/-! ## Nat packaging -/

/-- Cheeger `2s ≤ 5c` plus multiplicity `c ≤ 2g` is exactly Inv-5. -/
theorem mggF2_inv5_of_cheeger_and_double {s c g : ℕ}
    (hch : 2 * s ≤ 5 * c) (hmul : c ≤ 2 * g) : s ≤ 5 * g := by omega

/-- Cheeger `2s ≤ 5c` plus the sharper budget `5c ≤ 8g` gives Inv-4. -/
theorem mggF2_inv4_of_cheeger_and_eighth {s c g : ℕ}
    (hch : 2 * s ≤ 5 * c) (hmul : 5 * c ≤ 8 * g) : s ≤ 4 * g := by omega

/-- Inv-4 by cases: small sets ride on a nonempty cut, large sets on `5c ≤ 8g`. -/
theorem mggF2_inv4_of_cheeger_cases {s c g : ℕ}
    (hch : 2 * s ≤ 5 * c) (hg : 1 ≤ g)
    (hcases : s ≤ 4 ∨ 5 * c ≤ 8 * g) : s ≤ 4 * g := by
  rcases hcases with hsmall | hbudget
  · omega
  · exact mggF2_inv4_of_cheeger_and_eighth hch hbudget

/-- Unconditional Inv-5 on the factor-2 simple graph for every `m ≥ 3`.
Cited nowhere from the unit-shear Inv-15 packaging: the inputs are
`mggF2_two_card_le_five_multiCut` and `mggF2MultiCutCard_le_two_mul_edgeBoundary`. -/
theorem mggF2Graph_hasExpansionInv5 {m : ℕ} (hm : 3 ≤ m) :
    HasExpansionInv (mggF2Graph m (lt_of_lt_of_le (by decide : 0 < 3) hm)) 5 := by
  intro S hne hhalf
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  exact mggF2_inv5_of_cheeger_and_double
    (mggF2_two_card_le_five_multiCut hm S hne hhalf)
    (mggF2MultiCutCard_le_two_mul_edgeBoundary hm0 S)

/-! ## Sharper rational bound on the Gabber-Galil spectral gap

`mggF2_cheeger_gap_ge_two_fifths` only gives `8 - 5√2 ≥ 4/5`, which is too coarse
for Inv-4. The density-restricted argument below needs `8 - 5√2 ≥ 0.9289`.
-/

/-- `√2 ≤ 1.41422`, from `70711² = 5000045521 > 5 · 10⁹`. -/
theorem mggF2_sqrt_two_le_bound : Real.sqrt 2 ≤ 70711 / 50000 := by
  have hle : (2 : ℝ) ≤ (70711 / 50000) ^ 2 := by norm_num
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 70711 / 50000)] at h

/-- The adjacency gap of the factor-2 shears is at least `0.9289`. -/
theorem mggF2_gap_ge_bound : (9289 : ℝ) / 10000 ≤ 8 - 5 * Real.sqrt 2 := by
  have h := mggF2_sqrt_two_le_bound
  linarith

/-- Density-restricted Inv-4, fully certified.

For `1000 · |S| ≤ 461 · m²` the mass factor `(m² - |S|) / m²` in
`mggF2MultiCut_ge_gap_mass` is at least `539 / 1000`, and
`2 · (9289 / 10000) · (539 / 1000) = 1.0013542 > 1`, so `|S| ≤ 2 · multiCut`.
Combining with the certified `multiCut ≤ 2 · |∂|` gives `|S| ≤ 4 · |∂|` without
any multiplicity assumption. The half-set hypothesis is not needed: the density
bound is strictly stronger than `2 · |S| ≤ m²` would be here. -/
theorem mggF2_card_le_four_mul_edgeBoundary_of_sparse {m : ℕ} (hm : 3 ≤ m)
    (S : Finset (Fin (m * m))) (hne : S.Nonempty)
    (hdens : 1000 * S.card ≤ 461 * (m * m)) :
    S.card ≤
      4 * (edgeBoundary (mggF2Graph m (lt_of_lt_of_le (by decide : 0 < 3) hm))
            S).card := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  letI : NeZero m := ⟨by omega⟩
  show S.card ≤ 4 * (edgeBoundary (mggF2Graph m hm0) S).card
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hNpos : (0 : ℝ) < (m : ℝ) * (m : ℝ) := mul_pos hmR hmR
  have hs0 : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast card_pos.mpr hne
  have hdensR : (1000 : ℝ) * (S.card : ℝ) ≤ 461 * ((m : ℝ) * (m : ℝ)) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hdens
    push_cast at h
    linarith
  have hgap := mggF2_gap_ge_bound
  have hq0 : (0 : ℝ) ≤ 8 - 5 * Real.sqrt 2 := by linarith
  have hspace : (0 : ℝ) ≤ 461 / 1000 * ((m : ℝ) * (m : ℝ)) - (S.card : ℝ) := by
    linarith
  have h1 : (539 / 1000 : ℝ) * (S.card : ℝ) ≤
      (S.card : ℝ) * (((m : ℝ) * (m : ℝ)) - (S.card : ℝ)) /
        ((m : ℝ) * (m : ℝ)) := by
    rw [le_div_iff₀ hNpos]
    nlinarith [mul_nonneg hs0.le hspace]
  have hmass : (8 - 5 * Real.sqrt 2) *
      ((S.card : ℝ) * (((m : ℝ) * (m : ℝ)) - (S.card : ℝ)) /
        ((m : ℝ) * (m : ℝ))) ≤ (mggF2MultiCutCard hm0 S : ℝ) :=
    mggF2MultiCut_ge_gap_mass hm S
  have ha : (9289 / 10000 : ℝ) * ((539 / 1000) * (S.card : ℝ)) ≤
      (8 - 5 * Real.sqrt 2) * ((539 / 1000) * (S.card : ℝ)) :=
    mul_le_mul_of_nonneg_right hgap (by positivity)
  have hb : (8 - 5 * Real.sqrt 2) * ((539 / 1000) * (S.card : ℝ)) ≤
      (8 - 5 * Real.sqrt 2) *
        ((S.card : ℝ) * (((m : ℝ) * (m : ℝ)) - (S.card : ℝ)) /
          ((m : ℝ) * (m : ℝ))) :=
    mul_le_mul_of_nonneg_left h1 hq0
  have hnat : S.card ≤ 2 * mggF2MultiCutCard hm0 S := by
    have hcast : (S.card : ℝ) ≤ ((2 * mggF2MultiCutCard hm0 S : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hdouble := mggF2MultiCutCard_le_two_mul_edgeBoundary hm0 S
  omega

end SATurday.ProofComplexity
