import Theory.ProofComplexity.MGG.Factor2Doubled
import Mathlib.Tactic

/-!
# Factor-2 torus lines: pure and mixed rows and columns (R2 Block A item 3)

Rows and columns of the torus `(Z/m)^2` are classified relative to a vertex set
`S` as pure-in (contained in `S`), pure-out (disjoint from `S`), or mixed.

Two counting facts are proved here.

- Every mixed row outside the special lines of `Factor2Doubled` contributes at
  least one non-doubled horizontal cut pair, via the discrete intermediate value
  argument on the cyclic row and the shear composition
  `mggF2_x_succ_via_shears`. Likewise for columns. Hence
  `multiCut + |mixedRows| + |mixedCols| ≤ 2 |edgeBoundary| + 4`
  (`mggF2MultiCutCard_add_mixed_le`).
- A pure-in row and a pure-out column cannot coexist, which yields the
  dichotomy `mggF2_lines_dichotomy`: when there are at most `k` mixed lines,
  either all `m` lines of one direction are mixed, or `S` contains almost all
  of both directions (`m (2m - k) ≤ 2 |S|`), or `S` sits in a `k/2 x k/2` box
  (`4 |S| ≤ k^2`).

The unit-shear loss lemmas of `MGG.lean` are not cited.

LOG: R2 Block A factor-2 line classification, mixed lines force non-doubled cut pairs
-/

namespace SATurday.ProofComplexity

open Classical
open Finset
open Fin.NatCast

/-! ## Discrete intermediate value on a cyclic line -/

/-- A proper nonempty subset of `Fin m` has an element whose successor leaves it. -/
theorem mggF2_exists_succ_not_mem {m : ℕ} [NeZero m] {A : Finset (Fin m)}
    (hne : A.Nonempty) (hnu : A ≠ univ) : ∃ x ∈ A, x + 1 ∉ A := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x₀, hx₀⟩ := hne
  have hall : ∀ n : ℕ, x₀ + (n : Fin m) ∈ A := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ n ih =>
      have hstep := hcon _ ih
      have hcast : ((n + 1 : ℕ) : Fin m) = (n : Fin m) + 1 := Nat.cast_succ n
      rw [hcast, ← add_assoc]
      exact hstep
  apply hnu
  refine eq_univ_iff_forall.mpr fun z => ?_
  have := hall (z - x₀).val
  rwa [Fin.cast_val_eq_self, add_sub_cancel] at this

/-! ## Row and column cells, pure and mixed lines -/

/-- Columns `x` with `(x, y) ∈ S`. -/
def mggF2RowCells {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) (y : Fin m) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun x => mggEncode hm (x, y) ∈ S

/-- Rows `y` with `(x, y) ∈ S`. -/
def mggF2ColCells {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) (x : Fin m) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun y => mggEncode hm (x, y) ∈ S

/-- Rows contained in `S`. -/
def mggF2RowIn {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun y => mggF2RowCells hm S y = univ

/-- Rows disjoint from `S`. -/
def mggF2RowOut {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun y => mggF2RowCells hm S y = ∅

/-- Rows meeting both `S` and its complement. -/
def mggF2RowMixed {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun y =>
    ¬ mggF2RowCells hm S y = univ ∧ ¬ mggF2RowCells hm S y = ∅

/-- Columns contained in `S`. -/
def mggF2ColIn {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun x => mggF2ColCells hm S x = univ

/-- Columns disjoint from `S`. -/
def mggF2ColOut {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) : Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun x => mggF2ColCells hm S x = ∅

/-- Columns meeting both `S` and its complement. -/
def mggF2ColMixed {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun x =>
    ¬ mggF2ColCells hm S x = univ ∧ ¬ mggF2ColCells hm S x = ∅

/-- Pure-in, pure-out, mixed rows partition the `m` rows. -/
theorem mggF2_row_partition {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (mggF2RowIn hm S).card + (mggF2RowOut hm S).card + (mggF2RowMixed hm S).card = m := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun y => mggF2RowCells hm S y = univ)
  have h2 := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m)).filter fun y => ¬ mggF2RowCells hm S y = univ)
    (fun y => mggF2RowCells hm S y = ∅)
  rw [filter_filter, filter_filter] at h2
  have e1 : ((univ : Finset (Fin m)).filter fun y =>
      ¬ mggF2RowCells hm S y = univ ∧ mggF2RowCells hm S y = ∅) = mggF2RowOut hm S := by
    refine filter_congr fun y _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hu => ?_, h⟩
      rw [hu] at h
      exact (Finset.Nonempty.ne_empty ⟨(0 : Fin m), mem_univ _⟩) h
  rw [card_univ, Fintype.card_fin] at h1
  rw [e1] at h2
  unfold mggF2RowIn mggF2RowMixed
  omega

/-- Pure-in, pure-out, mixed columns partition the `m` columns. -/
theorem mggF2_col_partition {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (mggF2ColIn hm S).card + (mggF2ColOut hm S).card + (mggF2ColMixed hm S).card = m := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun x => mggF2ColCells hm S x = univ)
  have h2 := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m)).filter fun x => ¬ mggF2ColCells hm S x = univ)
    (fun x => mggF2ColCells hm S x = ∅)
  rw [filter_filter, filter_filter] at h2
  have e1 : ((univ : Finset (Fin m)).filter fun x =>
      ¬ mggF2ColCells hm S x = univ ∧ mggF2ColCells hm S x = ∅) = mggF2ColOut hm S := by
    refine filter_congr fun x _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hu => ?_, h⟩
      rw [hu] at h
      exact (Finset.Nonempty.ne_empty ⟨(0 : Fin m), mem_univ _⟩) h
  rw [card_univ, Fintype.card_fin] at h1
  rw [e1] at h2
  unfold mggF2ColIn mggF2ColMixed
  omega

/-! ## Mass bounds from pure and mixed lines -/

/-- Each pure-in row contributes `m` vertices of `S`. -/
theorem mggF2_mul_rowIn_card_le {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) :
    m * (mggF2RowIn hm S).card ≤ S.card := by
  have hsub : ((mggF2RowIn hm S ×ˢ (univ : Finset (Fin m))).image
      fun p : Fin m × Fin m => mggEncode hm (p.2, p.1)) ⊆ S := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    obtain ⟨hy, _⟩ := mem_product.mp hp
    have hyu : mggF2RowCells hm S p.1 = univ := (mem_filter.mp hy).2
    have hx : p.2 ∈ mggF2RowCells hm S p.1 := by rw [hyu]; exact mem_univ _
    exact (mem_filter.mp hx).2
  have hinj : Set.InjOn (fun p : Fin m × Fin m => mggEncode hm (p.2, p.1))
      (↑(mggF2RowIn hm S ×ˢ (univ : Finset (Fin m))) : Set (Fin m × Fin m)) := by
    intro p _ q _ h
    have := congrArg (mggDecode hm) h
    simp only [mggDecode_encode, Prod.mk.injEq] at this
    exact Prod.ext this.2 this.1
  have := card_le_card hsub
  rw [card_image_of_injOn hinj, card_product, card_univ, Fintype.card_fin, mul_comm] at this
  exact this

/-- Each pure-in column contributes `m` vertices of `S`. -/
theorem mggF2_mul_colIn_card_le {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m))) :
    m * (mggF2ColIn hm S).card ≤ S.card := by
  have hsub : ((mggF2ColIn hm S ×ˢ (univ : Finset (Fin m))).image
      fun p : Fin m × Fin m => mggEncode hm (p.1, p.2)) ⊆ S := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    obtain ⟨hx, _⟩ := mem_product.mp hp
    have hxu : mggF2ColCells hm S p.1 = univ := (mem_filter.mp hx).2
    have hy : p.2 ∈ mggF2ColCells hm S p.1 := by rw [hxu]; exact mem_univ _
    exact (mem_filter.mp hy).2
  have hinj : Set.InjOn (fun p : Fin m × Fin m => mggEncode hm (p.1, p.2))
      (↑(mggF2ColIn hm S ×ˢ (univ : Finset (Fin m))) : Set (Fin m × Fin m)) := by
    intro p _ q _ h
    have := congrArg (mggDecode hm) h
    simp only [mggDecode_encode, Prod.mk.injEq] at this
    exact Prod.ext this.1 this.2
  have := card_le_card hsub
  rw [card_image_of_injOn hinj, card_product, card_univ, Fintype.card_fin, mul_comm] at this
  exact this

/-- Without pure-in lines, `S` sits inside the mixed-column by mixed-row box. -/
theorem mggF2_card_le_mixed_mul {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m)))
    (hrow : mggF2RowIn hm S = ∅) (hcol : mggF2ColIn hm S = ∅) :
    S.card ≤ (mggF2ColMixed hm S).card * (mggF2RowMixed hm S).card := by
  have hsub : S ⊆ (mggF2ColMixed hm S ×ˢ mggF2RowMixed hm S).image
      fun p : Fin m × Fin m => mggEncode hm p := by
    intro v hv
    refine mem_image.mpr ⟨mggDecode hm v, ?_, mggEncode_decode hm v⟩
    have hv' : mggEncode hm ((mggDecode hm v).1, (mggDecode hm v).2) ∈ S := by
      rw [show ((mggDecode hm v).1, (mggDecode hm v).2) = mggDecode hm v from rfl,
        mggEncode_decode]
      exact hv
    refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩,
      mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩⟩
    · intro hu
      have hx : (mggDecode hm v).1 ∈ mggF2ColIn hm S := mem_filter.mpr ⟨mem_univ _, hu⟩
      rw [hcol] at hx
      exact notMem_empty _ hx
    · intro he
      have hy : (mggDecode hm v).2 ∈ mggF2ColCells hm S (mggDecode hm v).1 :=
        mem_filter.mpr ⟨mem_univ _, hv'⟩
      rw [he] at hy
      exact notMem_empty _ hy
    · intro hu
      have hy : (mggDecode hm v).2 ∈ mggF2RowIn hm S := mem_filter.mpr ⟨mem_univ _, hu⟩
      rw [hrow] at hy
      exact notMem_empty _ hy
    · intro he
      have hx : (mggDecode hm v).1 ∈ mggF2RowCells hm S (mggDecode hm v).2 :=
        mem_filter.mpr ⟨mem_univ _, hv'⟩
      rw [he] at hx
      exact notMem_empty _ hx
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_product]

/-- A pure-in row and a pure-out column would share a cell. -/
theorem mggF2_colOut_eq_empty_of_rowIn {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) (hne : (mggF2RowIn hm S).Nonempty) :
    mggF2ColOut hm S = ∅ := by
  obtain ⟨y, hy⟩ := hne
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have hyu := (mem_filter.mp hy).2
  have hxe := (mem_filter.mp hx).2
  have h1 : x ∈ mggF2RowCells hm S y := by rw [hyu]; exact mem_univ _
  have h2 : y ∈ mggF2ColCells hm S x := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h1).2⟩
  rw [hxe] at h2
  exact notMem_empty _ h2

/-- A pure-in column and a pure-out row would share a cell. -/
theorem mggF2_rowOut_eq_empty_of_colIn {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) (hne : (mggF2ColIn hm S).Nonempty) :
    mggF2RowOut hm S = ∅ := by
  obtain ⟨x, hx⟩ := hne
  refine eq_empty_of_forall_notMem fun y hy => ?_
  have hxu := (mem_filter.mp hx).2
  have hye := (mem_filter.mp hy).2
  have h1 : y ∈ mggF2ColCells hm S x := by rw [hxu]; exact mem_univ _
  have h2 : x ∈ mggF2RowCells hm S y := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h1).2⟩
  rw [hye] at h2
  exact notMem_empty _ h2

/-- Few mixed lines force one of three shapes: a whole direction is mixed, `S`
holds almost all pure lines of both directions, or `S` sits in a small box. -/
theorem mggF2_lines_dichotomy {m : ℕ} [NeZero m] (hm : 0 < m) (S : Finset (Fin (m * m)))
    (k : ℕ) (hk : (mggF2RowMixed hm S).card + (mggF2ColMixed hm S).card ≤ k) :
    m ≤ (mggF2RowMixed hm S).card + (mggF2ColMixed hm S).card ∨
      m * (2 * m - k) ≤ 2 * S.card ∨ 4 * S.card ≤ k * k := by
  have hrp := mggF2_row_partition hm S
  have hcp := mggF2_col_partition hm S
  by_cases hR : (mggF2RowIn hm S).Nonempty
  · have hCO := mggF2_colOut_eq_empty_of_rowIn hm S hR
    rw [hCO, card_empty] at hcp
    by_cases hC : (mggF2ColIn hm S).Nonempty
    · have hRO := mggF2_rowOut_eq_empty_of_colIn hm S hC
      rw [hRO, card_empty] at hrp
      right; left
      have h1 := mggF2_mul_rowIn_card_le hm S
      have h2 := mggF2_mul_colIn_card_le hm S
      have h3 : 2 * m - k ≤ (mggF2RowIn hm S).card + (mggF2ColIn hm S).card := by omega
      calc
        m * (2 * m - k) ≤ m * ((mggF2RowIn hm S).card + (mggF2ColIn hm S).card) :=
          Nat.mul_le_mul_left m h3
        _ = m * (mggF2RowIn hm S).card + m * (mggF2ColIn hm S).card := mul_add _ _ _
        _ ≤ 2 * S.card := by omega
    · left
      rw [not_nonempty_iff_eq_empty] at hC
      rw [hC, card_empty] at hcp
      omega
  · rw [not_nonempty_iff_eq_empty] at hR
    by_cases hC : (mggF2ColIn hm S).Nonempty
    · left
      have hRO := mggF2_rowOut_eq_empty_of_colIn hm S hC
      rw [hRO, card_empty, hR, card_empty] at hrp
      omega
    · right; right
      rw [not_nonempty_iff_eq_empty] at hC
      have h := mggF2_card_le_mixed_mul hm S hR hC
      have h4 : 4 * ((mggF2ColMixed hm S).card * (mggF2RowMixed hm S).card) ≤
          ((mggF2RowMixed hm S).card + (mggF2ColMixed hm S).card) *
            ((mggF2RowMixed hm S).card + (mggF2ColMixed hm S).card) := by
        have hz : (4 * (((mggF2ColMixed hm S).card : ℤ) * ((mggF2RowMixed hm S).card : ℤ))) ≤
            (((mggF2RowMixed hm S).card : ℤ) + ((mggF2ColMixed hm S).card : ℤ)) *
              (((mggF2RowMixed hm S).card : ℤ) + ((mggF2ColMixed hm S).card : ℤ)) := by
          nlinarith [sq_nonneg (((mggF2RowMixed hm S).card : ℤ) - ((mggF2ColMixed hm S).card : ℤ))]
        exact_mod_cast hz
      have h5 := Nat.mul_le_mul hk hk
      calc
        4 * S.card ≤ 4 * ((mggF2ColMixed hm S).card * (mggF2RowMixed hm S).card) :=
          Nat.mul_le_mul_left 4 h
        _ ≤ k * k := h4.trans h5

/-! ## Non-doubled cut pairs and mixed lines -/

/-- Directed non-doubled cut pairs `(v, w)`, `v ∈ S`, `w` a single-label out-neighbor. -/
def mggF2NdCutPairs {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    Finset (Fin (m * m) × Fin (m * m)) :=
  mggF2Pairs S (mggF2NdOut hm S)

theorem mggF2NdCutPairs_card {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (mggF2NdCutPairs hm S).card = ∑ v ∈ S, (mggF2NdOut hm S v).card :=
  mggF2Pairs_card _ _

/-- Horizontal (same-row) and vertical (same-column) non-doubled pairs are disjoint. -/
theorem mggF2_hnd_add_vnd_card_le {m : ℕ} (hm : 0 < m) (S : Finset (Fin (m * m))) :
    ((mggF2NdCutPairs hm S).filter fun q =>
        (mggDecode hm q.2).2 = (mggDecode hm q.1).2).card +
      ((mggF2NdCutPairs hm S).filter fun q =>
        (mggDecode hm q.2).1 = (mggDecode hm q.1).1).card ≤
      (mggF2NdCutPairs hm S).card := by
  have h := card_filter_add_card_filter_not (s := mggF2NdCutPairs hm S)
    (fun q => (mggDecode hm q.2).2 = (mggDecode hm q.1).2)
  have hsub : ((mggF2NdCutPairs hm S).filter fun q =>
      (mggDecode hm q.2).1 = (mggDecode hm q.1).1) ⊆
      (mggF2NdCutPairs hm S).filter fun q =>
        ¬ (mggDecode hm q.2).2 = (mggDecode hm q.1).2 := by
    intro q hq
    obtain ⟨hqN, hx⟩ := mem_filter.mp hq
    refine mem_filter.mpr ⟨hqN, fun hy => ?_⟩
    obtain ⟨hv, hw⟩ := (mem_mggF2Pairs_iff _ _ q).mp hqN
    obtain ⟨_, _, hwn⟩ :=
      (mem_mggF2OutNeighbors_iff hm S q.1 q.2).mp (mem_filter.mp hw).1
    have heq : q.2 = q.1 := by
      rw [← mggEncode_decode hm q.2, ← mggEncode_decode hm q.1, Prod.ext hx hy]
    exact hwn (heq ▸ hv)
  have := card_le_card hsub
  omega

/-- A mixed non-special row yields a horizontal non-doubled cut pair with source in
that row: the discrete IVT gives `(x, y) ∈ S`, `(x + 1, y) ∉ S`, and the shear
composition `+(2y+1)` then `-2y` walks from the first to the second through a
midpoint; whichever of the two labeled steps leaves `S` is the pair. -/
theorem mggF2_exists_hnd_pair_of_mixed_row {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) {y : Fin m} (hy : y ∈ mggF2RowMixed hm S)
    (hspec : y ∉ mggF2SpecialLines m) :
    ∃ q ∈ mggF2NdCutPairs hm S,
      (mggDecode hm q.2).2 = (mggDecode hm q.1).2 ∧ (mggDecode hm q.1).2 = y := by
  obtain ⟨_, hnu, hne⟩ := mem_filter.mp hy
  obtain ⟨x, hx, hx1⟩ := mggF2_exists_succ_not_mem (nonempty_of_ne_empty hne) hnu
  have hu : mggEncode hm (x, y) ∈ S := (mem_filter.mp hx).2
  have hu2 : mggEncode hm (x + 1, y) ∉ S := fun h => hx1 (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hshear : mggF2Neighbor hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1) mggF2Xm2y =
      mggEncode hm (x + 1, y) := mggF2_x_succ_via_shears hm x y
  have hdu : (mggDecode hm (mggEncode hm (x, y))).2 = y := by rw [mggDecode_encode]
  have hdmid : (mggDecode hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1)).2 = y := by
    rw [mggF2Neighbor_horiz_same_y hm _ (by decide : mggF2Xp2y1 ∈ mggF2HorizGens), hdu]
  have hdu2 : (mggDecode hm (mggEncode hm (x + 1, y))).2 = y := by rw [mggDecode_encode]
  by_cases hmid : mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1 ∈ S
  · refine ⟨(mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1, mggEncode hm (x + 1, y)),
      ?_, ?_, hdmid⟩
    · refine (mem_mggF2Pairs_iff _ _ _).mpr ⟨hmid, ?_⟩
      dsimp only
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact (mem_mggF2OutNeighbors_iff hm S _ _).mpr ⟨mggF2Xm2y, hshear, hu2⟩
      · exact mggF2_fiber_card_le_one_of_horiz_not_special hm
          (fun h => hu2 (h ▸ hmid)) (by decide : mggF2Xm2y ∈ mggF2HorizGens) hshear
          (by rw [hdmid]; exact hspec)
    · show (mggDecode hm (mggEncode hm (x + 1, y))).2 =
        (mggDecode hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1)).2
      rw [hdu2, hdmid]
  · refine ⟨(mggEncode hm (x, y), mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1),
      ?_, ?_, hdu⟩
    · refine (mem_mggF2Pairs_iff _ _ _).mpr ⟨hu, ?_⟩
      dsimp only
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact (mem_mggF2OutNeighbors_iff hm S _ _).mpr ⟨mggF2Xp2y1, rfl, hmid⟩
      · exact mggF2_fiber_card_le_one_of_horiz_not_special hm
          (fun h => hmid (by rw [h]; exact hu)) (by decide : mggF2Xp2y1 ∈ mggF2HorizGens) rfl
          (by rw [hdu]; exact hspec)
    · show (mggDecode hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Xp2y1)).2 =
        (mggDecode hm (mggEncode hm (x, y))).2
      rw [hdmid, hdu]

/-- Column analogue of `mggF2_exists_hnd_pair_of_mixed_row`. -/
theorem mggF2_exists_vnd_pair_of_mixed_col {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) {x : Fin m} (hx : x ∈ mggF2ColMixed hm S)
    (hspec : x ∉ mggF2SpecialLines m) :
    ∃ q ∈ mggF2NdCutPairs hm S,
      (mggDecode hm q.2).1 = (mggDecode hm q.1).1 ∧ (mggDecode hm q.1).1 = x := by
  obtain ⟨_, hnu, hne⟩ := mem_filter.mp hx
  obtain ⟨y, hy, hy1⟩ := mggF2_exists_succ_not_mem (nonempty_of_ne_empty hne) hnu
  have hu : mggEncode hm (x, y) ∈ S := (mem_filter.mp hy).2
  have hu2 : mggEncode hm (x, y + 1) ∉ S := fun h => hy1 (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hshear : mggF2Neighbor hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1) mggF2Ym2x =
      mggEncode hm (x, y + 1) := mggF2_y_succ_via_shears hm x y
  have hdu : (mggDecode hm (mggEncode hm (x, y))).1 = x := by rw [mggDecode_encode]
  have hdmid : (mggDecode hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1)).1 = x := by
    rw [mggF2Neighbor_vert_same_x hm _ (by decide : mggF2Yp2x1 ∈ mggF2VertGens), hdu]
  have hdu2 : (mggDecode hm (mggEncode hm (x, y + 1))).1 = x := by rw [mggDecode_encode]
  by_cases hmid : mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1 ∈ S
  · refine ⟨(mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1, mggEncode hm (x, y + 1)),
      ?_, ?_, hdmid⟩
    · refine (mem_mggF2Pairs_iff _ _ _).mpr ⟨hmid, ?_⟩
      dsimp only
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact (mem_mggF2OutNeighbors_iff hm S _ _).mpr ⟨mggF2Ym2x, hshear, hu2⟩
      · exact mggF2_fiber_card_le_one_of_vert_not_special hm
          (fun h => hu2 (h ▸ hmid)) (by decide : mggF2Ym2x ∈ mggF2VertGens) hshear
          (by rw [hdmid]; exact hspec)
    · show (mggDecode hm (mggEncode hm (x, y + 1))).1 =
        (mggDecode hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1)).1
      rw [hdu2, hdmid]
  · refine ⟨(mggEncode hm (x, y), mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1),
      ?_, ?_, hdu⟩
    · refine (mem_mggF2Pairs_iff _ _ _).mpr ⟨hu, ?_⟩
      dsimp only
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact (mem_mggF2OutNeighbors_iff hm S _ _).mpr ⟨mggF2Yp2x1, rfl, hmid⟩
      · exact mggF2_fiber_card_le_one_of_vert_not_special hm
          (fun h => hmid (by rw [h]; exact hu)) (by decide : mggF2Yp2x1 ∈ mggF2VertGens) rfl
          (by rw [hdu]; exact hspec)
    · show (mggDecode hm (mggF2Neighbor hm (mggEncode hm (x, y)) mggF2Yp2x1)).1 =
        (mggDecode hm (mggEncode hm (x, y))).1
      rw [hdmid, hdu]

/-- Mixed non-special rows inject (via source row) into horizontal non-doubled pairs. -/
theorem mggF2_rowMixed_sdiff_card_le_hnd {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (mggF2RowMixed hm S \ mggF2SpecialLines m).card ≤
      ((mggF2NdCutPairs hm S).filter fun q =>
        (mggDecode hm q.2).2 = (mggDecode hm q.1).2).card := by
  refine (card_le_card ?_).trans
    (card_image_le (f := fun q : Fin (m * m) × Fin (m * m) => (mggDecode hm q.1).2))
  intro y hy
  obtain ⟨hy, hspec⟩ := mem_sdiff.mp hy
  obtain ⟨q, hq, hrow, hqy⟩ := mggF2_exists_hnd_pair_of_mixed_row hm S hy hspec
  exact mem_image.mpr ⟨q, mem_filter.mpr ⟨hq, hrow⟩, hqy⟩

/-- Mixed non-special columns inject (via source column) into vertical non-doubled pairs. -/
theorem mggF2_colMixed_sdiff_card_le_vnd {m : ℕ} [NeZero m] (hm : 0 < m)
    (S : Finset (Fin (m * m))) :
    (mggF2ColMixed hm S \ mggF2SpecialLines m).card ≤
      ((mggF2NdCutPairs hm S).filter fun q =>
        (mggDecode hm q.2).1 = (mggDecode hm q.1).1).card := by
  refine (card_le_card ?_).trans
    (card_image_le (f := fun q : Fin (m * m) × Fin (m * m) => (mggDecode hm q.1).1))
  intro x hx
  obtain ⟨hx, hspec⟩ := mem_sdiff.mp hx
  obtain ⟨q, hq, hcol, hqx⟩ := mggF2_exists_vnd_pair_of_mixed_col hm S hx hspec
  exact mem_image.mpr ⟨q, mem_filter.mpr ⟨hq, hcol⟩, hqx⟩

/-- Mixed lines are at most the non-doubled cut pairs plus the four special lines. -/
theorem mggF2_mixed_card_le_nd_add_four {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    (mggF2RowMixed (lt_of_lt_of_le (by decide : 0 < 2) hm) S).card +
      (mggF2ColMixed (lt_of_lt_of_le (by decide : 0 < 2) hm) S).card ≤
      (mggF2NdCutPairs (lt_of_lt_of_le (by decide : 0 < 2) hm) S).card + 4 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hr := card_le_card_sdiff_add_card (s := mggF2RowMixed hm0 S) (t := mggF2SpecialLines m)
  have hc := card_le_card_sdiff_add_card (s := mggF2ColMixed hm0 S) (t := mggF2SpecialLines m)
  have hr' := mggF2_rowMixed_sdiff_card_le_hnd hm0 S
  have hc' := mggF2_colMixed_sdiff_card_le_vnd hm0 S
  have hsp := mggF2SpecialLines_card_le_two hm
  have hnd := mggF2_hnd_add_vnd_card_le hm0 S
  omega

/-- Second loss inequality: `multiCut + |mixedRows| + |mixedCols| ≤ 2 |edgeBoundary| + 4`.
Independent of the unit-shear loss lemmas. -/
theorem mggF2MultiCutCard_add_mixed_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (S : Finset (Fin (m * m))) :
    mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 2) hm) S +
        (mggF2RowMixed (lt_of_lt_of_le (by decide : 0 < 2) hm) S).card +
        (mggF2ColMixed (lt_of_lt_of_le (by decide : 0 < 2) hm) S).card ≤
      2 * (edgeBoundary (mggF2Graph m (lt_of_lt_of_le (by decide : 0 < 2) hm)) S).card + 4 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have h1 := mggF2MultiCutCard_add_sum_ndOut_le hm0 S
  have h2 := sum_mggF2OutNeighbors_card_le_edgeBoundary hm0 S
  have h3 := mggF2_mixed_card_le_nd_add_four hm S
  rw [mggF2NdCutPairs_card] at h3
  omega

end SATurday.ProofComplexity
