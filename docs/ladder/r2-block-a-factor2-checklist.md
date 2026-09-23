# R2 Block A checklist: factor-2 MGG to cubic Inv

Status: planning only. Do not start `satday auto` on the spectral pins
until steps 1 through 5 below are sorry-free proofs.

Rung: [r2-width-machinery.md](rungs/r2-width-machinery.md) (`Status: prose_accepted`).
Item 1 (Ben-Sasson–Wigderson) is already in the accepted tree. This checklist
covers Block A of item 2 (expander Tseitin via Margulis–Gabber–Galil), then
notes the separate random 3-CNF obligation.

Locked constants (do not weaken):

- `mggInvK := 4` in [theory/Theory/ProofComplexity/MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean)
- `mggInformativeFloor := 6` in the same file
- Downstream: `cubicInvK := 2` in [theory/Theory/ProofComplexity/Tseitin.lean](../../theory/Theory/ProofComplexity/Tseitin.lean)

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

- [ ] Define eight labeled factor-2 steps next to `mggNeighbor`, matching the
  AFP / Jimbo–Maruoka presentation already stubbed as
  `MGGFrontier.mggImport_mgg_graph_step` and `MGGFrontier.mggImport_mgg_graph`
  in [MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean).
- [ ] Reuse accepted encode and decode without duplication:
  `mggDecode`, `mggEncode`, `mggEncode_decode`, `mggDecode_encode`.
- [ ] Build the corresponding simple `FinGraph` and labeled multi-cut (the
  unit-shear analogues are `mggGraph`, `mggMultiCutCard`, `mggLeavingGens`).
- [ ] Prove connectivity for the factor-2 simple graph. Do not cite
  `mggGraph_isConnected` (that declaration is for the unit-shear graph).
- [ ] Leave the certified unit-shear surface untouched:
  `mggNeighbor`, `mggNeighbor_S_eq`, `mggNeighbor_T_eq`,
  `mggNeighbor_shear_loop_mem_axis`, near-axis excess lemmas, and related
  accepted decls in [accepted_declarations.txt](../../scripts/accepted_declarations.txt).

### 2. Multi-Cheeger from `gg_numerical_radius`

- [ ] Define the factor-2 adjacency Rayleigh form on torus coordinates (same
  shape as `mggMultiRayleigh` in
  [Spectral.lean](../../theory/Theory/ProofComplexity/MGG/Spectral.lean),
  but using the factor-2 steps / `ggAdj`).
- [ ] Prove the cut identity for set indicators: Rayleigh equals
  `8 · |S| − multiCut` (pattern:
  `mggMultiRayleigh_setIndicator`, `mgg_staySum_eq_eight_sub_leaving`,
  `sum_mggSetIndicator` in [Spectral.lean](../../theory/Theory/ProofComplexity/MGG/Spectral.lean)).
- [ ] Center the indicator (`sum_mggCenteredIndicator` pattern) and apply
  `gg_numerical_radius` from
  [Rayleigh.lean](../../theory/Theory/ProofComplexity/MGG/GG/Rayleigh.lean).
- [ ] For nonempty half-sets, obtain
  `multiCut ≥ ((8 − 5√2) / 2) · |S|`, hence `2 · |S| ≤ 5 · multiCut`.
- [ ] Package as a factor-2 analogue of accepted `MggHasMultiCheeger`; reuse
  the Nat ceiling `mgg_card_le_three_mul_of_two_fifth` and
  `mgg_card_le_three_mul_multiCut_of_cheeger` only after the cut type matches
  (those decls currently quantify over `mggMultiCutCard` on `mggNeighbor`).

### 3. Simple-graph Inv at locked `mggInvK = 4`

- [ ] Target: for every nonempty half-set `S` and every
  `m ≥ mggInformativeFloor`,
  `|S| ≤ mggInvK · |edgeBoundary G S|` on the factor-2 simple graph
  (`HasExpansionInv` in
  [FinGraph.lean](../../theory/Theory/ProofComplexity/FinGraph.lean)).
- [ ] Do not apply
  `mggGraph_hasExpansionInv_of_multi_cheeger_and_twelfth` until a twelfth
  reverse-loss witness exists for the factor-2 graph. That packaging needs
  `12 · reverseLoss ≤ |S|`.
- [ ] Do not stop at the Inv-15 packaging
  `mggGraph_hasExpansionInv15_of_multi_cheeger` (uses
  `mggReverseCutLoss_le_four_mul_edgeBoundary` on the unit shears).
- [ ] Prove a fresh multi-to-simple loss bound for the factor-2 generators.
  Unit-shear loss lemmas
  (`mggLeavingExcess_le_four`,
  `mggLeavingExcess_le_two_of_not_mem_nearAxis`,
  `mggReverseCutLoss_le_four_near_two_off`,
  `mggReverseCutLoss_le_two_mul_card_add_twelve_mul_m`) do not transfer.

### 4. Discharge Block A Frontier pins

- [ ] Replace both `sorry`s in [MGG.lean](../../theory/Theory/ProofComplexity/MGG.lean):
  - `MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil`
  - `MGGFrontier.mggGraph_hasExpansionInv`
  Retarget names and types to the factor-2 graph if the pin statements still
  mention `mggGraph` / `mggMultiCutCard`.
- [ ] Wire
  `exists_mgg_simple_hasExpansionInv_family_of_inv` (accepted) so
  `exists_mgg_simple_hasExpansionInv_family` packages connectivity plus Inv
  for the factor-2 graph.
- [ ] Delete or rewrite the three false-unit claims in
  [SpectralFrontier.lean](../../theory/Theory/ProofComplexity/MGG/SpectralFrontier.lean)
  (`numerical_radius_aux`, `has_multi_cheeger`,
  `hasExpansionInv_of_multi_cheeger`). `numerical_radius_aux` asserts the
  impossible unit-shear bound.

### 5. Certify the MGG pin only

- [ ] Run [scripts/check_axioms.sh](../../scripts/check_axioms.sh)
  (sorry only in Frontier-marked files; accepted decls only
  `propext`, `Classical.choice`, `Quot.sound`).
- [ ] Append new declarations to
  [scripts/accepted_declarations.txt](../../scripts/accepted_declarations.txt).
- [ ] Update plan truthfulness in
  [search/proof_sources/afp-expander-graphs-mgg/plans/accepted.json](../../search/proof_sources/afp-expander-graphs-mgg/plans/accepted.json)
  only for Lean decls that exist.
- [ ] Append a session entry to
  [r2-width-machinery.md](rungs/r2-width-machinery.md). Keep rung status
  `prose_accepted` until cubic and CS obligations below are also closed.
- [ ] Commit without push. Do not unkill the Saturday loop for spectral work.

### 6. Cubicization (only after step 5)

- [ ] Inhabit
  `TseitinFrontier.exists_cubic_hasExpansionInv_family` in
  [Tseitin.lean](../../theory/Theory/ProofComplexity/Tseitin.lean)
  at locked `cubicInvK = 2` and `cubicInvInformativeFloor`, using the factor-2
  MGG Inv family (replacement product / cubicization; not spectral invention).
- [ ] Discharge
  `TseitinFrontier.exists_tseitin_inv_expander_hard_family` via accepted
  `exists_tseitin_expander_hard_family_of_cubic_inv_expanders` in the same file
  (no new width proof).
- [ ] Only then may `satday auto` resume on cubicization, not on spectral pins.

### 7. Outside this Block A checklist

- [ ] `CSExpansionFrontier.exists_cs_clause_expanding_3cnf` in
  [CSExpansion.lean](../../theory/Theory/ProofComplexity/CSExpansion.lean)
  remains open. Packaging helpers
  `exists_cs_clause_expanding_3cnf_of_matchable_unsat_expanding` and
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` are accepted;
  the existence inhabitant is not.
- [ ] Rung item 2 is not certified until both the cubic Inv Tseitin pin and the
  random 3-CNF existence pin are sorry-free.

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
