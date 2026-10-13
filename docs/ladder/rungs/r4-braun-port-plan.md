# R4 Phase 2.1: port plan for Braun's Res(xor) bit pigeonhole bound

Source (credited in every ported docstring): K. Braun, bit pigeonhole lower bound for dag like
resolution over parities (arXiv 2609.23015), Lean development read from the local build at
`/Volumes/SSK Drive/braun-build/formalization` (read only, never copied wholesale, never
committed). Headline there: `MathResearch.bitPHP_superpolynomial` (`claims/BitPHPSuperpolynomial.lean`):
for every real `K > 0` and large `l`, every dag like Res(xor) refutation of the bit PHP CNF with
`n = 2^l` holes and `n + 1` pigeons has more than `n^K` nodes. Total Lean size there is about 8900
lines in `claims/` plus about 900 in `third-party-claims/` (chessboard homology).

## How his objects map onto ours

| Braun | Ours (on main) | Note |
| --- | --- | --- |
| `ParityClause V` = finset of affine maps, `clauseHolds` iff some `g x = 1` | `LClause` = finset of `(S, a)`, `lsatL` iff `lf S x = a` | `g = lf S + a + 1`; ours has variables in `N`, his in a finite type |
| `AffineDAG I C` (indexed by `Fin S`, rules initial / weaken / resolve / binary semantic) | `RL.Der`, `RL.Step`, `RL.DagRefutes` (finset of lines, rules ax / weak / res) | ours embeds into his; size `S <= card` after deduplication |
| `BitVar m l = Fin m x Fin l`, `usualCNFClause`, `usualBitPHPInitials` | `RL.bphpCNF l m` (variable `i*l+j`) | equal after the `finProdFinEquiv` reindexing and restriction of extra variables to 0 |
| bit PHP size `2^l + 1` pigeons | `RL.bphpCNF_unsat`, `bphp_dagRefutable` | non vacuity already on main |
| `PolynomialCalculus.*` (ordinary PC over `F_2`, truncated ENS spaces) | `Theory.ProofComplexity.PolyCalc` (PC over a field, degree `d`) | his needs multivariate polynomials with explicit joint degree and "reuse" and "substitution" lemmas; ours is a derivation predicate, partly reusable |
| matching moments, row linear spaces, cube residual separation | `Matching`, `Rado`, `ClosurePivot`, `LiftDup` are different technique (rank / Duplicator) | essentially no overlap: his bound goes by PC degree and a homological cover, ours by rank and sunflower style closure |
| `FiniteComplexCover`, chessboard star cover, augmented chains (homology) | none | new infrastructure |

The MAJ3 lifting / Rado / closure modules do not feed his proof; they prove a different
(lifted PHP) rank bound. His bit PHP bound is independent mathematics, so the port is almost
all new code on top of Mathlib.

## Layers, dependency order, rough size (his lines, ours will be 1.0 to 1.5 times)

0. Bridge (this task). `AffineForm`-free restatement: `PClause`, `PDag` (his `AffineDAG`), conversion
   `DagRefutes (bphpCNF l m) s -> PDag` on `BitVar m l` with `S <= s`, and the target `BraunBitPHP`
   as a `Prop` plus the corollary for our `DagRefutes`. About 300 lines. New file `BraunDag.lean`.
1. Affine and polynomial interface: `AffineForm` (98), `FiniteAffinePolynomial` (58),
   `FiniteAffineCoordinates` (90), `FiniteAffineSpan` (80), `AffineCoordinates` (138),
   `AffineSystemLinearAlgebra` (160). About 600 lines.
2. Ordinary PC foundations (R01 to R05): `PolynomialCalculus` (103), `...Reuse` (91),
   `...Substitution` (87), `...Duality` (35), `BooleanReduction` (201), `MpTelescoping` (103). About 650.
3. ENS blocks and affine clause registry (R06, R08, R16, R18): `FreshENSBlock` (177),
   `FreshENSScalarCleanup` (115), `LowRankENS` (218), `AffineClauseRegistry` (148),
   `AffineFamilyRemoval*` (220), `AffineBlockRestriction` (143). About 1100.
4. Clause rules to PC degree (R19 to R23): `BinaryAffineZeroCover` (137),
   `BinarySemanticAffineCover` (144), `AffineClauseCompression` (78), `AffineClauseResolution` (166),
   `AffineClauseWeakening` (114), `AffineDAGRegistry` (241). About 900.
5. Bit PHP initial bridge and transfer (R24): `CompactBitDecoder*` (320), `BitPHPInitialBridge` (158),
   `BitPHPClauseTransfer` (110). About 600.
6. Matching moments (R09, R10): `MatchingNormalForm` (332), `MatchingMomentCompleteness` (233),
   `...Cycles` (133), `...Extension` (264), `...Relabeling` (110), `MatchingFiltration` (112), plus
   the homology packages `AugmentedChains*`, `CoverDoubleComplex`, `FiniteComplexCover`, and
   third party `Chessboard*`, `HomologicalCover` (about 900). About 2500. The hardest layer.
7. Row linear space and separation (R11 to R15): `TwoRowInterpolation` (185), `RowLinearPolynomialSpace`
   (138), `DisjointCoordinatePairs` (135), `RowCube*` (475), `CubeResidualDualSeparation` (98),
   `CoordinateRestrictionIdeal`, `OrdinaryRestriction*`, `CommonAffineRestrictionKernel`,
   `RestrictionKernelBounds`. About 1600.
8. Assembly and parameters (R17, R25): `AffineFamilyExclusion` (78), `AffineParameterBounds` (118),
   `BitPHPExponential` (166), `BitPHPSuperpolynomial` (56). About 450.

## Status (updated after layer 7)

Merged on main: layers 0 to 5 and now most of layer 7 (all in `theory/Theory/ProofComplexity/Braun*.lean`,
about 6,100 Lean lines in total; layer 7 itself added about 2,300). Layer 7 files: `BraunTwoRow`
(`twoRow_interpolation`, forbidden pair certificate), `BraunRestriction` (coordinate and affine
restriction ideals, ordinary restriction dimension, `BlockRestrictionData`, `blockRestrictionData_exists`,
`affineInputRank_le`), `BraunRowLinear`, `BraunKernelBounds`, `BraunCommonKernel`
(`common_affine_restriction_kernel`), `BraunCubeDrop`, `BraunCoordPairs`, `BraunMatchingBase` (the
definitional prelude of layer 6: `Cell`, `exclusionBase`, `rowEquation`, `functionalUnaryBase_eq`),
`BraunRowCube`, `BraunRowCubeIsolation`, and `BraunCompactTransfer` (`compactDecoder_PC`, deferred from
layer 5). Not done in layer 7: `CubeResidualDualSeparation` (98 lines, his `cube_residual_dual_separation`),
because it uses `matching_normalized_annihilator` and `functionalUnary_pc_eq_ns` from layer 6.
Lesson from porting: his Lean/Mathlib is newer than ours in a few names (`totalDegree_finsetProd`,
`monomial_mul_monomial`, `Mathlib.Analysis.Real.Sqrt`), and `convert` / `exact` can time out on
classical versus subtype `DecidableEq` instances on cube sums; every layer so far compiled after
at most three such mechanical fixes per file.

Layer 6 part 1 (done, merged): `BraunMatchingNormalForm` (matching normal form, `IsMatching` stated directly,
row equation computations), `BraunMatchingMomentCompleteness` (with `annihilator_extension`),
`BraunMomentChains` (minimal augmented chain API on the chessboard: `Coeff`, `boundary`, `push`),
`BraunMatchingMomentCycles` (moment layers are cycles), `BraunMatchingMomentRelabeling`,
`BraunMatchingMomentExtension`, `BraunMatchingFiltration` (`functionalUnary_pc_eq_ns`,
`matching_normalized_annihilator`) and `BraunCubeResidualDualSeparation` (layer 7's deferred theorem).
Layer 6 part 2 (done, merged): the homology. `BraunAugComplex` (abstract augmented F2 complexes: `boundary`,
`boundary_boundary`, cones, simplex boundary exactness, relabeling `push`, `exactAt_subcomplex`), `BraunAugCover`
(nerve, intersections, the cover double complex, `homological_cover`), `BraunAugChessboard` (first row star cover,
star intersections, nerve is a simplex boundary, parameter arithmetic `chessboardNu`,
`chessboard_homological_bound`) and `BraunChessboardFilling` (`matchingMomentFilling : MatchingMomentFilling`, valid
for all `s >= 1`, plus unconditional wrappers `matching_normalized_annihilator_unconditional`,
`functionalUnary_no_pc_refutation_unconditional`, `cube_residual_dual_separation_unconditional`). All new
declarations are in namespace `SATurday.ProofComplexity.BraunPC.Aug` (except the final bridge). The earlier
theorems keep their `hfill` argument; pass `matchingMomentFilling`. Layer 6 is complete. Remaining: layer 8 only.

Layer 6 (matching moments and homology), original estimate. Remaining his lines: `MatchingNormalForm`
(332, minus the prelude already ported), `MatchingMomentCompleteness` (233), `...Cycles` (133),
`...Extension` (264), `...Relabeling` (110), `MatchingFiltration` (112), `PolynomialCalculusDuality`
linear separation, plus the homology packages (`AugmentedChains*`, `CoverDoubleComplex`,
`FiniteComplexCover`, third party `Chessboard*`, `HomologicalCover`, about 900 combined) that depend on
Mathlib homological algebra or hand rolled chain complexes. Total about 2,300 to 2,600 his lines, so
2,500 to 3,500 ours. This is the hardest layer: the moment/cycle files are combinatorial and port
mechanically at the rate seen above (about 1,000 lines per session), but the homology part has no
Mathlib analog we can lean on and carries the main risk (a dedicated chessboard complex homology
development; if it stalls, a fallback is to state the single acyclicity input as an explicit `Prop`
hypothesis, as the plan allows for conditional corollaries). Order inside layer 6: normal form and
completeness, then extension/relabeling/filtration (unblocks `cube_residual_dual_separation`), then
homology last. Suggested budget: 3 to 4 sessions.

Layer 8 (assembly and parameters), honest estimate: `AffineFamilyExclusion` (78), `AffineParameterBounds`
(118), `BitPHPExponential` (166), `BitPHPSuperpolynomial` (56), about 420 his lines, 450 to 600 ours.
Mostly real analysis inequalities (log, exp, ceil sqrt) in the style of `BraunKernelBounds`, which already
compiles here, so low risk, but it can only be finished once layer 6 and `cube_residual_dual_separation`
exist, since the final theorem composes them with layers 4, 5 and 7. Suggested budget: 1 session after
layer 6.

Order: 0, then 1 -> 2 -> 3 -> 4 -> 5 in a chain; 6 and 7 can proceed in parallel after 2; 8 last.
Estimated total 8000 to 9000 Lean lines. Layers 0 to 8 are merged (layer 6 homology proved, `matchingMomentFilling`; layer 8 assembly gives `braunBitPHP`).

## Layer 8 status and statement fidelity check (2026-10-13)

Layer 8 is done: `BraunParameterBounds` (`uniformKernel`, `eventually_affine_parameters`,
`bitPHP_exponential_room`) and `BraunAssembly` (`registry_system_eq_ensFamily`,
`affine_family_exclusion_of_square`, `affine_family_exclusion`, `affine_family_polylog_exclusion`,
`bitPHP_exponential`, `bitPHP_exponential_base_two`, `bitPHP_superpolynomial`, then
`RL.Braun.braunBitPHP : BraunBitPHP`, `bphp_dag_superpolynomial`, `bphp_dag_exponential`). All use
`matchingMomentFilling` through `cube_residual_dual_separation_unconditional`; nothing is conditional.

Fidelity check against his `bitPHP_superpolynomial` and `bitPHP_exponential`:
* `BraunBitPHP` is his `bitPHP_superpolynomial` verbatim in shape: `K > 0`, `exists L`, `forall l >= L`,
  `n + 1 = 2^l + 1` pigeons, `l` bits per pigeon (`BitVar (2^l+1) l`), initial clauses `usualInitials`,
  a node family `C : Fin S -> clause` (not required injective), a node `f` with `C f = empty`, and the
  strict bound `(2^l)^K < S` with the real power `Real.rpow`. No constant was changed.
* The exponential form is proved with his constants: for `l >= 32` (his explicit threshold), `S >
  exp(2^l / (32768 l^2))`, and base two. The threshold `l >= 32` is a hypothesis of `bphp_dag_exponential`
  and `bitPHP_exponential`; the superpolynomial form only asserts a threshold `L` exists, as in his.
* Mismatch 1 (type valued vs prop valued): his `AffineDAG` is `Type` valued, our `PDag` is `Prop` valued.
  Equivalent for these statements (`pdag_to_affineDAG`); the exponential and superpolynomial theorems
  are stated for `PDag`, which is the weaker looking but equal hypothesis.
* Mismatch 2 (what the size counts): in his theorems `S` is the number of nodes (indexed family, repeats
  allowed). Ours for `RL.DagRefutes` is `s`, the number of lines of a finset based derivation. The
  bridge `bphp_dag_to_pdag` gives a dag with `S <= s` nodes, so the bound on `S` implies the same bound on
  `s`; the corollary about `DagRefutes` is therefore at least as strong a statement in the direction of
  lower bounds (it bounds `s`, which is `>= S`).
* Mismatch 3 (calculus): our `RL.DagRefutes` has the rules axiom, weakening, resolution; his `PDag` has
  also a binary semantic rule and semantic weakening. Our refutations embed into his, so his bound
  applies to ours; the converse is not claimed.
* Mismatch 4 (variables): `bphpCNF l m` uses variables `i*l+j` in `N`, translated to `BitVar m l` by
  `finProdFinEquiv` with all extra variables read as 0; this is the dictionary of `BraunDag`.
No claim is weakened. Nothing here is certified; the gate status is reported separately.

## Policy notes

* Each ported file carries a docstring crediting the Braun source file and statement; where our
  proof differs, say so. Theorem statements keep his quantifier shape so fidelity can be checked.
* Do not import his modules; reprove in `Theory.ProofComplexity.*` with unique names.
* An unproved layer is never stated as an axiom or `sorry` on the accepted tree; only `Prop`
  definitions (for example `BraunBitPHP`) and conditional corollaries.
* Statement fidelity risk: his clause truth convention is `g x = 1`; ours is `lf S x = a`. The
  bridge theorem fixes the dictionary once and all later layers use his convention.
