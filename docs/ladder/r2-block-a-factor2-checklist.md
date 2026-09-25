# R2 Block A checklist: factor-2 MGG to cubic Inv

Status: Block A items 1-7 closed. Item 6 inhabited the cubic Inv family at
`mggF2CubK = 164` and floor `1968`. Item 7 restated the CS pin off the
false Cluster 23 equations (`α = 1`, `r = n / 16`) and inhabited it from
the Tseitin Inv hard family. Human gate merge_certified applied 2026-09-25.
Rung status is `certified`. Do not start `satday auto` unless explicitly asked.

Rung: [r2-width-machinery.md](rungs/r2-width-machinery.md) (`Status: certified`).
Item 1 (Ben-Sasson–Wigderson) is already in the accepted tree. This checklist
covers Block A of item 2 (expander Tseitin via Margulis–Gabber–Galil), then
notes the separate random 3-CNF obligation (archival).

Locked constants (do not weaken):

- `mggInvK := 4` in [theory/Theory/ProofComplexity/MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean)
- `mggInformativeFloor := 6` in the same file
- Downstream: `cubicInvK := mggF2CubK` (164) and
  `cubicInvInformativeFloor := mggF2CubFloor` (1968) in
  [Tseitin.lean](../../theory/Theory/ProofComplexity/Tseitin.lean). The
  2026-09-08 inhabit plan authorizes this raise when cubicization of Inv-4
  only yields `kCub > 2`. Full-cloud lifts of half-sets multiply the cut
  ratio by 8, so `k = 2` is false for the cycle replacement.

## Why the unit-shear pins cannot use the new spectral proof

`mggNeighbor` in [MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean) is the
unit-shear star: `(±1,0)`, `(0,±1)`, `±S`, `±T`. The Gabber–Galil constant
`5√2` is proved for the factor-2 shears. Exact second eigenvalues of the unit
adjacency already exceed `5√2` at `m = 12`, so
`|mggMultiRayleigh f| ≤ 5√2 · mggRealNormSq f` is false for that neighbor.

The proved radius lives here:

- [theory/Theory/ProofComplexity/MGG/GG/Rayleigh.lean](../../theory/Theory/ProofComplexity/MGG/GG/Rayleigh.lean)
  (`gg_numerical_radius`, `ggAdj`)
- Supporting Fourier and Young modules:
  [DFT.lean](../../theory/Theory/ProofComplexity/MGG/GG/DFT.lean),
  [YoungDefs.lean](../../theory/Theory/ProofComplexity/MGG/GG/YoungDefs.lean),
  [Young.lean](../../theory/Theory/ProofComplexity/MGG/GG/Young.lean),
  [YoungAssembly.lean](../../theory/Theory/ProofComplexity/MGG/GG/YoungAssembly.lean)

Accepted declarations to reuse when retargeting are listed in
[scripts/accepted_declarations.txt](../../scripts/accepted_declarations.txt)
(from `mggDecode` through `mggGraph_hasExpansionInv15_of_multi_cheeger`).

---

## Checklist

### 1. Factor-2 graph on the same vertex set

- [x] Define eight labeled factor-2 steps next to `mggNeighbor`, matching the
  AFP / Jimbo–Maruoka presentation already stubbed as
  `MGGFrontier.mggImport_mgg_graph_step` and `MGGFrontier.mggImport_mgg_graph`
  in [MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean).
  Implemented as `mggF2Neighbor` in
  [MGG/Factor2.lean](../../theory/Theory/ProofComplexity/MGG/Factor2.lean)
  (cross-ref on `mggNeighbor` docstring).
- [x] Reuse accepted encode and decode without duplication:
  `mggDecode`, `mggEncode`, `mggEncode_decode`, `mggDecode_encode`.
- [x] Build the corresponding simple `FinGraph` and labeled multi-cut (the
  unit-shear analogues are `mggGraph`, `mggMultiCutCard`, `mggLeavingGens`).
  Factor-2: `mggF2Graph`, `mggF2MultiCutCard`, `mggF2LeavingGens`.
- [x] Prove connectivity for the factor-2 simple graph. Do not cite
  `mggGraph_isConnected` (that declaration is for the unit-shear graph).
  Certified: `mggF2Graph_isConnected` via shear composition unit walks.
- [x] Leave the certified unit-shear surface untouched:
  `mggNeighbor`, `mggNeighbor_S_eq`, `mggNeighbor_T_eq`,
  `mggNeighbor_shear_loop_mem_axis`, near-axis excess lemmas, and related
  accepted decls in [accepted_declarations.txt](../../scripts/accepted_declarations.txt).

### 2. Multi-Cheeger from `gg_numerical_radius`

- [x] Define the factor-2 adjacency Rayleigh form on torus coordinates (same
  shape as `mggMultiRayleigh` in
  [Spectral.lean](../../theory/Theory/ProofComplexity/MGG/Spectral.lean),
  but using the factor-2 steps / `ggAdj`).
  Implemented as `mggF2MultiRayleigh` and `mggF2MultiRayleigh_eq_ggAdj` in
  [MGG/Factor2Spectral.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Spectral.lean).
- [x] Prove the cut identity for set indicators: Rayleigh equals
  `8 · |S| − multiCut` (pattern:
  `mggMultiRayleigh_setIndicator`, `mgg_staySum_eq_eight_sub_leaving`,
  `sum_mggSetIndicator` in [Spectral.lean](../../theory/Theory/ProofComplexity/MGG/Spectral.lean)).
  Factor-2: `mggF2_staySum_eq_eight_sub_leaving`, `mggF2MultiRayleigh_setIndicator`.
- [x] Center the indicator (`sum_mggCenteredIndicator` pattern) and apply
  `gg_numerical_radius` from
  [Rayleigh.lean](../../theory/Theory/ProofComplexity/MGG/GG/Rayleigh.lean).
  `mggF2MultiRayleigh_centered`, `mggF2_centered_eq_eight_norm_sub_cut`,
  `mggF2_centered_numerical_radius`.
- [x] For nonempty half-sets, obtain
  `multiCut ≥ ((8 − 5√2) / 2) · |S|`, hence `2 · |S| ≤ 5 · multiCut`.
  `mggF2MultiCut_ge_gap_mass`, `mggF2MultiCut_ge_half_gap`,
  `mggF2_two_card_le_five_multiCut` for `3 ≤ m`.
- [x] Package as a factor-2 analogue of accepted `MggHasMultiCheeger`; reuse
  the Nat ceiling `mgg_card_le_three_mul_of_two_fifth` and
  `mgg_card_le_three_mul_multiCut_of_cheeger` only after the cut type matches
  (those decls currently quantify over `mggMultiCutCard` on `mggNeighbor`).
  `MggF2HasMultiCheeger` quantifies over `mggF2MultiCutCard`.
  `mggF2_hasMultiCheeger` inhabits it for `3 ≤ m`.
  `mggF2_card_le_three_mul_multiCut_of_cheeger` calls
  `mgg_card_le_three_mul_of_two_fifth`. The unit-shear
  `mgg_card_le_three_mul_multiCut_of_cheeger` is not applied.

### 3. Simple-graph Inv at locked `mggInvK = 4`

Loss and sparse Inv-4 live in
[MGG/Factor2Inv.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Inv.lean).
Doubled-edge count lives in
[MGG/Factor2Doubled.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Doubled.lean).
Line dichotomy lives in
[MGG/Factor2Lines.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Lines.lean).
Locked Inv-4 packaging lives in
[MGG/Factor2Inv4.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Inv4.lean).

- [x] Prove a fresh multi-to-simple loss bound for the factor-2 generators.
  Unit-shear loss lemmas
  (`mggLeavingExcess_le_four`,
  `mggLeavingExcess_le_two_of_not_mem_nearAxis`,
  `mggReverseCutLoss_le_four_near_two_off`,
  `mggReverseCutLoss_le_two_mul_card_add_twelve_mul_m`) do not transfer and are
  not cited. Certified chain, standard axioms only:
  `mggF2OutNeighbors`, `mggF2LeavingExcess`, `mggF2ReverseCutLoss`,
  `mggF2MultiCutCard_eq_sum_out_add_reverseLoss`,
  `mggF2_labels_to_ne_neighbor_card_le_two` (non-loop fibers have size at most
  two), `mggF2LeavingGens_card_le_two_mul_outNeighbors_of_mem`,
  `mggF2ReverseCutLoss_le_sum_outNeighbors`,
  `sum_mggF2OutNeighbors_card_le_edgeBoundary` (directed cut pair injection),
  `mggF2ReverseCutLoss_le_edgeBoundary`,
  `mggF2MultiCutCard_le_two_mul_edgeBoundary`.
- [x] Do not apply
  `mggGraph_hasExpansionInv_of_multi_cheeger_and_twelfth`. Not cited; no twelfth
  witness is claimed for the factor-2 graph.
- [x] Do not stop at the Inv-15 packaging
  `mggGraph_hasExpansionInv15_of_multi_cheeger` (uses
  `mggReverseCutLoss_le_four_mul_edgeBoundary` on the unit shears). Not cited.
  The unconditional factor-2 packaging is `mggF2Graph_hasExpansionInv5`
  (Inv-5, certified for every `m ≥ 3`), strictly better than Inv-15.
- [x] Cut positivity for nonempty half-sets from factor-2 connectivity only:
  `mggF2_edgeBoundary_card_pos` via `mggF2Graph_isConnected`.
- [x] Sparse-regime Inv-4, certified: `mggF2_gap_ge_bound`
  (`8 − 5√2 ≥ 0.9289`, sharper than `mggF2_cheeger_gap_ge_two_fifths`) and
  `mggF2_card_le_four_mul_edgeBoundary_of_sparse`, which proves
  `|S| ≤ 4 · |∂S|` whenever `1000 · |S| ≤ 461 · m²`.
- [x] Target: for every nonempty half-set `S` and every
  `m ≥ mggInformativeFloor`,
  `|S| ≤ mggInvK · |edgeBoundary G S|` on the factor-2 simple graph
  (`HasExpansionInv` in
  [FinGraph.lean](../../theory/Theory/ProofComplexity/FinGraph.lean)).
  Certified in
  [MGG/Factor2Inv4.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Inv4.lean)
  as `mggF2Graph_hasExpansionInv`. No `sorry`. The 8/5 multiplicity pin was
  not needed: dense-band Inv-4 uses additive loss
  `multiCut ≤ |∂| + 2m` (`mggF2MultiCutCard_le_edgeBoundary_add_two_mul` in
  [Factor2Doubled.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Doubled.lean))
  for `m ≥ 19`, and line-count loss plus `mggF2_lines_dichotomy` in
  [Factor2Lines.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Lines.lean)
  for `6 ≤ m ≤ 18`. The `Factor2InvFrontier` 8/5 statement was deleted.

### 4. Discharge Block A Frontier pins

- [x] Replace both `sorry`s in [MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean):
  - `MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil`
  - `MGGFrontier.mggGraph_hasExpansionInv`
  Retarget names and types to the factor-2 graph if the pin statements still
  mention `mggGraph` / `mggMultiCutCard`.
  Discharged in [Factor2Inv4.lean](../../theory/Theory/ProofComplexity/MGG/Factor2Inv4.lean):
  types are `MggF2HasMultiCheeger` and `HasExpansionInv (mggF2Graph m _) mggInvK`.
  Unit-shear sorry stubs removed from `MGG.lean`.
- [x] Wire
  `exists_mgg_simple_hasExpansionInv_family_of_inv` (accepted) so
  `exists_mgg_simple_hasExpansionInv_family` packages connectivity plus Inv
  for the factor-2 graph.
  Retargeted `of_inv` and family to `mggF2Graph` / `mggF2Graph_isConnected`
  in `Factor2Inv4.lean`; `MGGFrontier.exists_mgg_simple_hasExpansionInv_family`
  aliases the top-level family.
- [x] Delete or rewrite the three false-unit claims in
  [SpectralFrontier.lean](../../theory/Theory/ProofComplexity/MGG/SpectralFrontier.lean)
  (`numerical_radius_aux`, `has_multi_cheeger`,
  `hasExpansionInv_of_multi_cheeger`). `numerical_radius_aux` asserts the
  impossible unit-shear bound.
  Deleted; module now points at `mggF2_hasMultiCheeger` and
  `mggF2Graph_hasExpansionInv` only. No `sorry`.

### 5. Certify the MGG pin only

- [x] Run [scripts/check_axioms.sh](../../scripts/check_axioms.sh)
  (sorry only in Frontier-marked files; accepted decls only
  `propext`, `Classical.choice`, `Quot.sound`).
- [x] Append new declarations to
  [scripts/accepted_declarations.txt](../../scripts/accepted_declarations.txt).
- [x] Update plan truthfulness in
  [search/proof_sources/afp-expander-graphs-mgg/plans/accepted.json](../../search/proof_sources/afp-expander-graphs-mgg/plans/accepted.json)
  only for Lean decls that exist.
- [x] Append a session entry to
  [r2-width-machinery.md](rungs/r2-width-machinery.md). Keep rung status
  `prose_accepted` until cubic and CS obligations below are also closed.
- [x] Commit without push. Do not unkill the Saturday loop for spectral work.

### 6. Cubicization (only after step 5)

- [x] Inhabit
  `TseitinFrontier.exists_cubic_hasExpansionInv_family` in
  [Tseitin.lean](../../theory/Theory/ProofComplexity/Tseitin.lean)
  from cycle cubicization of `mggF2Graph` in
  [Cubicize.lean](../../theory/Theory/ProofComplexity/MGG/Cubicize.lean).
  Charging gives `mggF2CubK = 164` (`|T| ≤ 32|∂C| + 33·Σ c ≤ 164|∂C|`)
  and `mggF2CubFloor = 1968` so `tseitinInvWidthFloor n 164 > 3`.
  `cubicInvK` and `cubicInvInformativeFloor` are aliases of those defs.
  `k = 2` is not inhabited.
- [x] Discharge
  `TseitinFrontier.exists_tseitin_inv_expander_hard_family` via accepted
  `exists_tseitin_expander_hard_family_of_cubic_inv_expanders` in the same file
  (no new width proof).
- [ ] Only then may `satday auto` resume on cubicization, not on spectral pins.
  Not started.

### 7. Outside this Block A checklist

- [x] `CSExpansionFrontier.exists_cs_clause_expanding_3cnf` in
  [CSExpansion.lean](../../theory/Theory/ProofComplexity/CSExpansion.lean)
  is sorry-free after the 2026-09-25 restatement. Cluster 23 equations
  `α = 1` and `r = n / 16` are killed (archival
  `exists_cs_clause_expanding_3cnf_cluster23`). The live pin is the cubic
  Inv Tseitin hard family: unbounded unsat width-3 CNF with
  `3 < tseitinInvWidthFloor n cubicInvK`. Packaging helpers
  `exists_cs_clause_expanding_3cnf_of_matchable_unsat_expanding` and
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` stay
  accepted and unused. `exists_spreads_matchable_unsat_random3CNF` stays
  archival `sorry`. `satday auto` stays off.
- [x] Rung item 2 existence pins are sorry-free: cubic Inv Tseitin (item 6)
  and the restated CS pin (item 7). Rung status `certified` after
  merge_certified 2026-09-25.

---

## Explicit non-goals

- Do not weaken `mggInvK` from 4 to 15.
- Do not cite AFP Isabelle theorems as Lean axioms.
- Do not auto-translate Isabelle; the factor-2 Lean proof already exists under
  `MGG/GG/`.
- Do not delete or re-prove accepted unit-shear lemmas in order to reuse their
  names for factor-2 generators.
- Do not mark deferred AFP import-ladder steps done in `accepted.json` unless
  corresponding Lean declarations exist.
