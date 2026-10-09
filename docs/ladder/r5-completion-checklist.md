# R5 completion plan (manual)

Status: certified (2026-10-06, axiom gate green; theorem 1 both directions, theorem 2),
matching `docs/ladder/ladder.md`.

**Outcome:** Bridge pins A and B are closed and Block C is certified:
`bridge_theorem_2`, `TAUT_in_coNP`, the easy direction of theorem 1
(`proofSystemOfNPVerifier`), and the hard direction (`bridge_theorem_1_hard`,
Cook Levin coNP to TAUT reduction in `Bridge/Hard.lean`). Zero Bridge sorries.
Restarting `satday auto` remains an operator decision (last item below).

## Files

- `theory/Theory/ProofComplexity/Bridge/ProofSystem.lean` (pins A and B)
- `theory/Theory/ProofComplexity/Bridge/CookReckhow.lean` (theorem 2, `TAUT_in_coNP`,
  easy direction), `Bridge/Hard.lean` and supporting modules (hard direction)
- Gate: `lake build` + `scripts/check_axioms.sh`

## Open Frontier pins

- none in `ProofSystem.lean` (soft pin B closed 2026-09-29)

## Checklist

### A. Hard pin — `validatesTautologyResult_computableInPolyTime` (~6102)

- [x] Inventory reuse: `padBitsComputer` / `padBitsComputableInPolyTime`,
  `bitsEqualPairComputableInPolyTime`, `pow2BitsLE` / `writePow2Bits`,
  `natBitsLE` / `lengthBitsEqPow2`, `countLengthBits`, leftover drain,
  encodePair load, reject / tautology slices
- [x] Build `evalOn` FinTM2 (Stmt + step lemmas + `EvalsToInTime`) for
  `PropFormula.evalOn` (via `evalEncoded` interpreter:
  `evalEncodedComputer` / `evalEncoded_computableInPolyTime`)
- [x] Index-loop sequencer under `|table|` fuel
  (`validatesTautology_by_index_pad` path; functional `indexValidate` /
  `indexValidateFuel` + one-iter `indexStepBitsComputer` certified;
  `odometerSucc` / `odometerSucc_assignmentAt` certified;
  `odometerSuccComputer` EvalsToInTime + `odometerSuccComputableInPolyTime`;
  local `comp_idBitEnc_idBitEnc` available for glue;
  Remaining: `indexValidateComputer` FinTM2 under `|table|` fuel)
- [x] Glue decode-pair → decode-formula → length gate → loop →
  accept / reject into one `FinTM2` + poly `time`
  (via `comp_idBitEnc_idBitEnc` of `decodePairResult` with
  `afterDecodePairResult`; functional equality + outBound certified;
  `afterDecodePairResultComputer` fail-tag Evals certified;
  encodePair parse load certified (`adr_evals_load_encodePair`);
  parse-fail Evals (`false::[]`, `false::[true]`);
  success-tag reject scaffold Evals under
  `validatesTautologyResult = [true]`
  (`afterDecodePairResult_evals_encodePair_reject`);
  `afterParse` → `allTrueScan` / `allTrueOk` / `clearWork` certified
  (false-in-table and all-true stub-reject both reach `[true]`);
  `allTrueOk` → `lenLoop` length-count certified;
  `lenFinish` → `pow2Check` shape gate certified (`pow2BitsLE` form
  `false* ++ [true]`; success parks `pow2BitsLE n` on `inp` at `pow2Ok` →
  `maxVarGate` (stub-rejects via `clearInp`);
  `maxVarSuccBits` / `bitsEqual_pow2BitsLE_iff` functional certified;
  `maxVarOfCode` / `maxVarSuccBitsOfCode` /
  `bitsEqual_pow2BitsLE_maxVarSuccBits` / `lengthGateOk_iff_bitsEqual_parked`
  functional certified;
  ADR labels and Stmt landed for parkWidth, maxVar scan, bitsEqual,
  index loop, prefix eval, `failDrain`, `acceptPrep`, `idxInc`
  (`maxVarGate` still stub-rejects so the reject scaffold stays green);
  parkWidth / copyLeft / revCode / failDrain Evals certified;
  `adr_evals_park_to_mvParse` reaches `mvParse` with `out = φCode`
  and parked `reverse(pow2BitsLE n) ++ table`;
  `mvNat` lockstep rewritten: delimiter on `left`, refund via
  `mvNatRefund`, grow via `mvNatRestTake` / `mvNatRest` /
  `mvNatDiscardPark` (handles `n > k > 0`); step lemmas certified;
  `adr_evals_mvNat` / `_le` / `_gt` / refund / rest / drain Evals
  certified (`work` becomes `true^{max k n}`);
  `adr_evals_mvParse_formula` certified on `encodeFormula` with shared
  width budget `M` (`k ≤ M`, `φ.maxVar ≤ M`, time
  `32 * (L+1) * (M+2)`);
  `adr_evals_mvToPow2` / `adr_evals_unpark` / `adr_evals_eq_pow2` /
  `adr_evals_mvParse_to_indexLoop` certified (matching width
  `n = φ.maxVar + 1` enters `indexLoop` with assignment `false^n`);
  index loop Evals certified: `adr_evals_evParse_formula`,
  `adr_evals_index_one_true`, `adr_evals_indexLoop_allTrue`
  (all-true table plus tautology reaches `acceptEmit`);
  `maxVarGate` wired to `parkWidth` via `maxVarDump` (`pow2BitsLE n` on
  `inp`); reject scaffold split: malformed `pow2Check`, false-in-table,
  and non-power-of-two length still emit `[true]`;
  `adr_evals_allTrue_pow2_to_parkWidth` certified (all-true length `2^n`
  reaches `parkWidth` with `pow2BitsLE n`);
  `adr_evals_park_to_accept` certified (matching width tautology plus
  all-true table reaches `false :: encodeFormula φ`);
  `afterDecodePairResult_evals_encodePair_accept` certified from the
  success tag through halt;
  leftover true drain, general pair-parse fail, width mismatch zipper,
  `adr_evals_index_one_false`, decode-formula fail
  (`adr_evals_mvParse_decode_none`,
  `afterDecodePairResult_evals_encodePair_decode_fail`), and width
  mismatch encodePair glue
  (`afterDecodePairResult_evals_encodePair_width_ne`) are certified;
  non-tautology index walk (`adr_evals_indexLoop_notTaut`),
  park-to-reject (`adr_evals_park_to_notTaut`), and encodePair glue
  (`afterDecodePairResult_evals_encodePair_notTaut`) are certified;
  `afterDecodePairResultComputableInPolyTime` packaged with `outputsFun`
  covering fail-tag, parse-fail, malformed table, decode-formula fail,
  width mismatch, non-tautology, and tautology accept)
- [x] Package
  `TM2ComputableInPolyTime idBitEnc idBitEnc validatesTautologyResult_on_pair`
  (local `comp_idBitEnc_idBitEnc` of `decodePairResult` with
  `afterDecodePairResult`; no mathlib `.comp`)
- [x] Remove sorry; commit

### B. Soft pin — `truthTable_is_prop_proof_system`

- [x] Derive TT-map poly witness from A (or thin wrapper over
  `validatesTautologyResult_on_pair` + seed emits)
  (`liftValidationToTT` strips `false :: φCode` and otherwise emits
  `encodeFormula tautSeed`; `truthTableProofSystem_eq_liftValidationToTT`;
  `liftValidationToTTComputer` in `2|s| + 11` steps;
  `comp_idBitEnc_idBitEnc` with
  `validatesTautologyResult_on_pairComputableInPolyTime`)
- [x] Package
  `⟨{ poly := …, sound := truthTableProofSystem_sound,
  complete := truthTableProofSystem_complete }⟩`
  (`truthTableProofSystemComputableInPolyTime` as `poly`)
- [x] Confirm `truthTable_not_poly_bounded` still green
  (`lake build Theory.ProofComplexity.Bridge.ProofSystem`)
- [x] Remove sorry; commit

### C. R5 finish (after A+B)

- [x] Add `CookReckhow.lean` with bridge theorem 2 and `TAUT_in_coNP`
  (`sanitizeComputer` lifted decode + eval + notBit; axiom gate PASS)
- [x] Easy direction of theorem 1: package `proofSystemOfNPVerifier` as
  `TM2ComputableInPolyTime idBitEnc idBitEnc` (functional sound,
  complete, polyBound, and `afterDecodeProofSystem` composition certified;
  `unaryLEComputableInPolyTime` certified under `encodePair`;
  `toUnaryComputableInPolyTime` certified; `unaryMulRevComputableInPolyTime`
  certified under `encodePair`; `unaryScaleComputableInPolyTime` certified
  (nested push Stmt; time `|s|+1`); `polyDomBound` / `lengthOkDom` semantic;
  `scaleAppendComputableInPolyTime` / `polyEvalUnaryLinearComputableInPolyTime`
  certified (degree ≤ 1 exact unary poly-eval; time `|s|+2`);
  `polyEvalUnary_divX` Horner identity certified;
  `polyEvalUnaryConstComputableInPolyTime` /
  `polyEvalUnaryDegLeOneComputableInPolyTime` certified;
  `unaryPow_two_toUnary` semantic identity certified;
  `lengthOk_linear` / `lengthOk_of_natDegree_le_one` certified;
  `lengthOkLinearPair` glue toward unaryLE composition certified;
  `lengthOkLinearPairComputer` FinTM2 scaffold landed (parse, scale, emit);
  scale, emit, reverse, parse, and loadRight Evals certified;
  `lengthOkLinearPairComputableInPolyTime` packaged under `encodePair`;
  `lengthOkLinearComputableInPolyTime` certified (prep then `unaryLE` via
  `seqCompComputer`); `lengthOkDegLeOneComputableInPolyTime` certified;
  `TAUT_in_NP_of_NP_eq_coNP` / `isPropProofSystemOfNPVerifier` /
  `bridge_theorem_1_easy_of_packaging` semantic packaging certified;
  `andBitComputer` / `andBitComputableInPolyTime` certified (acceptWitness
  AND glue); `swapPair` semantic rearrange certified (`(φ,π) ↦ (π,φ)`);
  `swapPairComputer` FinTM2 scaffold landed (parse, park, emit, reverse);
  parse, loadRight, park, and emit Evals certified; reverse phase Evals
  certified; `swapPairComputableInPolyTime` packaged under `encodePair`;
  `dupEncodePairComputableInPolyTime` packaged (`s ↦ encodePair (s,s)`);
  `mapFstToUnaryComputableInPolyTime` packaged under `encodePair`;
  `toUnarySelfPairComputableInPolyTime` via seqComp of dup and mapFst;
  Horner scaleAppend semantic identity and quadratic closed form certified;
  `toUnaryDupPairComputableInPolyTime` and `unarySquareComputableInPolyTime`
  packaged (`true^(n^2)`); `polyEvalUnaryXSquaredComputableInPolyTime` and
  `polyEvalUnaryXSquaredPlusConstComputableInPolyTime` packaged;
  `mapFstScaleAppendComputableInPolyTime` packaged under `encodePair`
  (`(x,y) ↦ (true^(a*|x|+b), y)`); `mapSndScaleAppendComputableInPolyTime`
  via swap compose (`(φ,π) ↦ (φ, true^(a*|π|+b))`);
  `polyEvalUnaryQuadraticComputableInPolyTime` packaged (Horner
  `a X^2 + b X + c`);   `mapFstComputableInPolyTime` packaged under
  `encodePair` (product `mapFstComputer` host parse park copyIn guest
  copyOut emit rev); `mapSndComputableInPolyTime` via swap compose;
  Horner `polyEvalUnaryComputableInPolyTime` WF for arbitrary p
  (toUnarySelfPair, mapSnd IH, unaryMul, scaleAppend 1 coeff0);
  `lengthOkComputableInPolyTime` for opaque p (swap, mapSnd polyEval,
  unaryLE); `afterDecodeProofSystemComputableInPolyTime`, `sanitizeProofComputableInPolyTime`,
  `npProofSystemComputableInPolyTime`, `bridge_theorem_1_easy` and
  unconditional `summit_corollary` certified 2026-10-05; axiom gate PASS)
- [x] Hard direction of theorem 1: Cook Levin style coNP to TAUT reduction
  (`Bridge/CookLevin.lean`, 2026-10-05: generic output length bound
  `outBound_of_computable` (stack growth per step, `stepBudget`),
  `proofCheckComputableInPolyTime` (apply `f`, swap, `bitsEqualPair`), and
  unconditional `TAUT_in_NP_of_polyBounded'` certified; axiom gate PASS;
  remaining: Cook Levin reduction `L ∈ NP → complement L ≤p TAUT`
  (tableau formula of a FinTM2 run, computed by a poly time FinTM2) plus
  closure of `InNP` under poly many one reductions, then
  `bridge_theorem_1_hard : (∃ f, IsPropProofSystem f ∧ PolynomiallyBounded f) → ClassNP_eq_ClassCoNP`)
  Cook Levin plan (2026-10-06), sub-checklist, in order:
  - [x] `Bridge/StackProg.lean`: structured Bool stack programs (`Prog`), big
    step `Exec` with instruction cost, assembly, compilation to `FinTM2`
    (`progTM`, `progTM_outputs`), cleanup of junk stacks, `Computes.toPoly`
    packaging into `TM2ComputableInPolyTime idBitEnc idBitEnc`. Machines are now
    verified at program level, not phase by phase.
  - [x] Unary / emission library over `Prog` (copy, add, emit bits, for-loop
    invariant lemma `exec_loop_inv`).
  - [x] `Bridge/Tableau.lean`: coded machine `CM` (windows of depth `c`, top
    relative arrays, no height variables), tableau constraint list `consL` built
    from register relative templates `TF`, soundness and completeness
    (`tabFormula_taut_iff`: tautology iff no accepting witness).
  - [x] `tm → CM` simulation (semantic only): reachable symbol lists, window
    interpreter, `stepAux` window lemma, halting frozen, acceptance iff output.
  - [x] Generator `Prog` emitting that bit string, `Computes` certified.
  - [x] `complement L ≤p TAUT` for `L ∈ NP`; `InNP` closed under it;
    `bridge_theorem_1_hard`.
- [x] Wire into `Theory.lean`; axiom gate PASS; zero Bridge sorries
- [x] Update rung memory; R5 certified 2026-10-06 (`bridge_theorem_1_hard` in `Bridge/Hard.lean`; axiom gate PASS, 2016 declarations)
- [ ] Only then consider `satday auto` again (operator decision)

## Order rule

A → B → C. Soft pin is blocked on A's poly witness. One micro-lemma commit
at a time; refuse drafts that cite unknown identifiers.
