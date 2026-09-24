import Theory.ProofComplexity.MGG.Factor2Lines
import Mathlib.Tactic

/-!
# Factor-2 simple-graph Inv at locked `mggInvK = 4` (R2 Block A item 3, closed)

Fully certified `HasExpansionInv (mggF2Graph m _) mggInvK` for every
`m ≥ mggInformativeFloor`. No `sorry`, no Frontier namespace.

Inputs, all certified upstream:

- spectral mass bound `mggF2MultiCut_ge_gap_mass` with `8 - 5 sqrt 2 ≥ 0.9289`
  (`mggF2_gap_ge_bound`), converted to the Nat inequality
  `9289 |S| (m^2 - |S|) ≤ 10000 m^2 multiCut` (`mggF2_spectral_nat`);
- sparse regime `1000 |S| ≤ 461 m^2`:
  `mggF2_card_le_four_mul_edgeBoundary_of_sparse`;
- dense band `461 m^2 < 1000 |S| ≤ 500 m^2`:
  - `m ≥ 19`: the additive loss `multiCut ≤ |edgeBoundary| + 2m`
    (`mggF2MultiCutCard_le_edgeBoundary_add_two_mul`) and the polynomial identity
    `4 [s (27156 M - 37156 s) - 4289 M^2] = (74312 s - 17156 M)(M - 2 s)`;
  - `6 ≤ m ≤ 18`: the line-count loss
    `multiCut + |mixedRows| + |mixedCols| ≤ 2 |edgeBoundary| + 4`
    (`mggF2MultiCutCard_add_mixed_le`), the pure/mixed dichotomy
    `mggF2_lines_dichotomy` at `k = 4` and `k = 8`, and exhaustive
    `interval_cases` over `(m, |S|)`.

The unit-shear loss lemmas of `MGG.lean`, `mggGraph_hasExpansionInv15_of_multi_cheeger`,
and `mggGraph_hasExpansionInv_of_multi_cheeger_and_twelfth` are not cited.

LOG: R2 Block A factor-2 Inv-4 closed, sparse via density, dense via additive loss and line dichotomy
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Nat form of the spectral cut bound -/

/-- `9289 |S| (m^2 - |S|) ≤ 10000 m^2 multiCut`, from the real mass bound. -/
theorem mggF2_spectral_nat {m : ℕ} (hm : 3 ≤ m) (S : Finset (Fin (m * m))) :
    9289 * (S.card * (m * m - S.card)) ≤
      10000 * ((m * m) * mggF2MultiCutCard (lt_of_lt_of_le (by decide : 0 < 3) hm) S) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  letI : NeZero m := ⟨by omega⟩
  have hsM : S.card ≤ m * m := (card_le_univ S).trans (by simp)
  have hmass := mggF2MultiCut_ge_gap_mass hm S
  have hNpos : (0 : ℝ) < (m : ℝ) * m := by positivity
  have hgap := mggF2_gap_ge_bound
  have hsR : (S.card : ℝ) ≤ (m : ℝ) * m := by exact_mod_cast hsM
  have hnn : (0 : ℝ) ≤ (S.card : ℝ) * ((m * m : ℝ) - S.card) / (m * m : ℝ) := by
    apply div_nonneg (mul_nonneg (by positivity) ?_) hNpos.le
    linarith
  have h1 : (9289 / 10000 : ℝ) * ((S.card : ℝ) * ((m * m : ℝ) - S.card) / (m * m : ℝ)) ≤
      (mggF2MultiCutCard hm0 S : ℝ) :=
    (mul_le_mul_of_nonneg_right hgap hnn).trans hmass
  have key : (9289 / 10000 : ℝ) * ((S.card : ℝ) * ((m * m : ℝ) - S.card) / (m * m : ℝ)) *
      (10000 * ((m : ℝ) * m)) = 9289 * ((S.card : ℝ) * ((m * m : ℝ) - S.card)) := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 10000 * ((m : ℝ) * m))
  rw [key] at h2
  have hcast : ((9289 * (S.card * (m * m - S.card)) : ℕ) : ℝ) ≤
      ((10000 * ((m * m) * mggF2MultiCutCard hm0 S) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hsM]
    linarith
  exact_mod_cast hcast

/-! ## Numeric closure of the dense band -/

/-- Dense band, `m ≥ 19`: additive loss `c ≤ g + 2m` suffices. The key identity is
`4 [s (27156 M - 37156 s) - 4289 M^2] = (74312 s - 17156 M)(M - 2 s) ≥ 0` on the band,
and `4289 m ≥ 80000` for `m ≥ 19`. -/
theorem mggF2_dense_large_nat (m s c g : ℕ) (hm : 19 ≤ m) (hd : 461 * (m * m) < 1000 * s)
    (hhalf : 2 * s ≤ m * m) (hsp : 9289 * (s * (m * m - s)) ≤ 10000 * ((m * m) * c))
    (hL1 : c ≤ g + 2 * m) : s ≤ 4 * g := by
  by_contra hcon
  have hg : 4 * g + 1 ≤ s := by omega
  have hsM : s ≤ m * m := by omega
  zify [hsM] at hsp hd hhalf hg hL1 hm
  have hM0 : (0 : ℤ) ≤ (m : ℤ) * m := by positivity
  have h1 : (10000 : ℤ) * ((m : ℤ) * m) * c ≤ 10000 * ((m : ℤ) * m) * (g + 2 * m) :=
    mul_le_mul_of_nonneg_left hL1 (by positivity)
  have h2 : (4 : ℤ) * ((m : ℤ) * m) * g ≤ ((m : ℤ) * m) * (s - 1) := by
    have := mul_le_mul_of_nonneg_left hg hM0
    linarith
  have h3 : (0 : ℤ) ≤ (74312 * (s : ℤ) - 17156 * ((m : ℤ) * m)) * ((m : ℤ) * m - 2 * s) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : (0 : ℤ) ≤ ((m : ℤ) * m) * ((m : ℤ) * (4289 * m - 80000)) :=
    mul_nonneg hM0 (mul_nonneg (by positivity) (by linarith))
  have h5 : (0 : ℤ) < (m : ℤ) * m := by positivity
  nlinarith

/-- Dense band, `6 ≤ m ≤ 18`: line-count loss `c + t ≤ 2g + 4` with the pure/mixed
dichotomy at `k = 4` and `k = 8`, closed by exhaustive case analysis on `(m, s)`. -/
theorem mggF2_dense_small_nat (m s c g t : ℕ) (hm6 : 6 ≤ m) (hm18 : m ≤ 18)
    (hd : 461 * (m * m) < 1000 * s) (hhalf : 2 * s ≤ m * m)
    (hsp : 9289 * (s * (m * m - s)) ≤ 10000 * ((m * m) * c))
    (hL2 : c + t ≤ 2 * g + 4)
    (hd4 : 4 < t ∨ m ≤ t ∨ m * (2 * m - 4) ≤ 2 * s ∨ 4 * s ≤ 4 * 4)
    (hd8 : 8 < t ∨ m ≤ t ∨ m * (2 * m - 8) ≤ 2 * s ∨ 4 * s ≤ 8 * 8) : s ≤ 4 * g := by
  have hlo : 461 * (m * m) / 1000 + 1 ≤ s := by omega
  have hhi : s ≤ m * m / 2 := by omega
  interval_cases m <;> norm_num at hlo hhi hd4 hd8 hsp ⊢ <;> interval_cases s <;> omega

/-! ## Inv-4 on the factor-2 simple graph -/

/-- Factor-2 simple-graph Inv at locked `mggInvK = 4` for every
`m ≥ mggInformativeFloor`. Fully certified: sparse sets by
`mggF2_card_le_four_mul_edgeBoundary_of_sparse`, the dense band by
`mggF2_dense_large_nat` (`m ≥ 19`) and `mggF2_dense_small_nat` (`6 ≤ m ≤ 18`).
Does not cite `mggGraph_hasExpansionInv15_of_multi_cheeger` or
`mggGraph_hasExpansionInv_of_multi_cheeger_and_twelfth`. -/
theorem mggF2Graph_hasExpansionInv {m : ℕ} (hm : mggInformativeFloor ≤ m) :
    HasExpansionInv
      (mggF2Graph m (lt_of_lt_of_le (by decide : 0 < mggInformativeFloor) hm))
      mggInvK := by
  intro S hne hhalf
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < mggInformativeFloor) hm
  have hm6 : 6 ≤ m := by simpa [mggInformativeFloor] using hm
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  letI : NeZero m := ⟨by omega⟩
  show S.card ≤ mggInvK * (edgeBoundary (mggF2Graph m hm0) S).card
  rw [show mggInvK = 4 from rfl]
  by_cases hdens : 1000 * S.card ≤ 461 * (m * m)
  · exact mggF2_card_le_four_mul_edgeBoundary_of_sparse hm3 S hne hdens
  have hd : 461 * (m * m) < 1000 * S.card := not_le.mp hdens
  have hsp : 9289 * (S.card * (m * m - S.card)) ≤
      10000 * ((m * m) * mggF2MultiCutCard hm0 S) := mggF2_spectral_nat hm3 S
  by_cases hm19 : 19 ≤ m
  · have hL1 : mggF2MultiCutCard hm0 S ≤ (edgeBoundary (mggF2Graph m hm0) S).card + 2 * m :=
      mggF2MultiCutCard_le_edgeBoundary_add_two_mul hm2 S
    exact mggF2_dense_large_nat m S.card _ _ hm19 hd hhalf hsp hL1
  · have hm18 : m ≤ 18 := by omega
    have hL2 : mggF2MultiCutCard hm0 S + (mggF2RowMixed hm0 S).card +
        (mggF2ColMixed hm0 S).card ≤ 2 * (edgeBoundary (mggF2Graph m hm0) S).card + 4 :=
      mggF2MultiCutCard_add_mixed_le hm2 S
    have hL2' : mggF2MultiCutCard hm0 S +
        ((mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card) ≤
        2 * (edgeBoundary (mggF2Graph m hm0) S).card + 4 := by omega
    have hd4 : 4 < (mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card ∨
        m ≤ (mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card ∨
        m * (2 * m - 4) ≤ 2 * S.card ∨ 4 * S.card ≤ 4 * 4 := by
      by_cases h : (mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card ≤ 4
      · exact Or.inr (mggF2_lines_dichotomy hm0 S 4 h)
      · exact Or.inl (not_le.mp h)
    have hd8 : 8 < (mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card ∨
        m ≤ (mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card ∨
        m * (2 * m - 8) ≤ 2 * S.card ∨ 4 * S.card ≤ 8 * 8 := by
      by_cases h : (mggF2RowMixed hm0 S).card + (mggF2ColMixed hm0 S).card ≤ 8
      · exact Or.inr (mggF2_lines_dichotomy hm0 S 8 h)
      · exact Or.inl (not_le.mp h)
    exact mggF2_dense_small_nat m S.card _ _ _ hm6 hm18 hd hhalf hsp hL2' hd4 hd8

end SATurday.ProofComplexity
