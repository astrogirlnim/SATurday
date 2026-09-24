import Theory.ProofComplexity.MGG.Factor2Inv4
import Mathlib.Tactic

/-!
# MGG spectral notes (unit-shear dead end closed)

The Gabber-Galil constant `5√2` is proved for the factor-2 shears
(`MGGGabberGalil.gg_numerical_radius`). It does **not** apply to
`mggNeighbor`: the unit shears already have second eigenvalue above `5√2`
at `m = 12`, so the old unit-shear Frontier claims

- `|mggMultiRayleigh f| ≤ 5√2 · mggRealNormSq f`
- `MggHasMultiCheeger` from that radius
- Inv-4 from unit-shear multi Cheeger plus twelfth loss

were false as stated and have been deleted.

Certified Block A surface (factor-2):

- `mggF2_hasMultiCheeger` / `MggF2HasMultiCheeger`
- `mggF2Graph_hasExpansionInv` at locked `mggInvK = 4`
- `exists_mgg_simple_hasExpansionInv_family`
- discharged historical names
  `MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil` and
  `MGGFrontier.mggGraph_hasExpansionInv` (types retargeted to factor-2)

No `sorry` remains in this module.

LOG: R2 Block A SpectralFrontier false-unit claims deleted
-/

namespace SATurday.ProofComplexity.MGGSpectralFrontier

/-- Pointer: factor-2 multi Cheeger from Gabber-Galil radius. -/
abbrev has_multi_cheeger := @mggF2_hasMultiCheeger

/-- Pointer: locked Inv-4 on the factor-2 simple graph. -/
abbrev hasExpansionInv := @mggF2Graph_hasExpansionInv

end SATurday.ProofComplexity.MGGSpectralFrontier
