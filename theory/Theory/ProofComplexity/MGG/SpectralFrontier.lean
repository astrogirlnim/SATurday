import Theory.ProofComplexity.MGG.Spectral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# MGG spectral Frontier

Hoory numerical radius and the Inv-4 glue stay here. The Rayleigh form and the
cut identity live in `MGG.Spectral` and call accepted encode, decode, neighbor,
and leaving-generator declarations.

LOG: R2 manual AFP port Phase C Frontier WIP
-/

namespace SATurday.ProofComplexity.MGGSpectralFrontier

open Classical Finset Real SATurday.ProofComplexity

/-- The `5√2` numerical radius is proved for the factor-2 Gabber-Galil steps
in `MGGGabberGalil.gg_numerical_radius`. It does not apply to `mggNeighbor`:
the unit shears `(±1,0)`, `(0,±1)`, `±S`, `±T` have second eigenvalue above
`5√2` already at `m = 12`. This statement is that stronger claim. -/
theorem numerical_radius_aux {m : ℕ} [NeZero m] (hm : 0 < m) (f : MggTorus m → ℝ)
    (_hmean : ∑ p : MggTorus m, f p = 0) :
    |mggMultiRayleigh hm f| ≤ 5 * Real.sqrt 2 * mggRealNormSq f := by
  sorry

/-- `MggHasMultiCheeger` from the numerical-radius bound on the centered indicator. -/
theorem has_multi_cheeger (m : ℕ) (hm0 : 0 < m) (_hm : mggInformativeFloor ≤ m) :
    MggHasMultiCheeger m hm0 := by
  letI : NeZero m := ⟨ne_of_gt hm0⟩
  intro S hne hhalf
  have hmean := sum_mggCenteredIndicator hm0 S
  have hrad := numerical_radius_aux hm0 (mggCenteredIndicator hm0 S) hmean
  -- `mggMultiRayleigh_setIndicator` plus centering gives
  -- `multiCut ≥ (8 - 5√2) * normSq`, and half-sets turn that into `2|S| ≤ 5 multiCut`.
  sorry

/-- Axis-aware Inv-4 from multi Cheeger, using accepted twelfth packaging. -/
theorem hasExpansionInv_of_multi_cheeger {m : ℕ} (hm : 3 ≤ m)
    (hcheeger : MggHasMultiCheeger m (lt_of_lt_of_le (by decide : 0 < 3) hm)) :
    HasExpansionInv (mggGraph m (lt_of_lt_of_le (by decide : 0 < 3) hm)) mggInvK := by
  intro S hne hhalf
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have _h3 := mgg_card_le_three_mul_multiCut_of_cheeger hm0 hcheeger S hne hhalf
  -- Accepted `mggGraph_hasExpansionInv_of_multi_cheeger_and_twelfth` applies once
  -- `12 * mggReverseCutLoss hm0 S ≤ S.card` is proved for these half-sets.
  sorry

end SATurday.ProofComplexity.MGGSpectralFrontier
