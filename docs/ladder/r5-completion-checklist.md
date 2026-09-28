# R5 completion plan (manual)

Status: active (diverted from `satday auto`; sticky formalize force cleared)

**Constraint:** only two Bridge sorries left, both in
`theory/Theory/ProofComplexity/Bridge/ProofSystem.lean`. Do not invent
`Turing.*` names; reuse certified helpers named in the pin comments. Close
the hard pin first; the soft pin is packaging.

## Files

- Edit: `theory/Theory/ProofComplexity/Bridge/ProofSystem.lean`
- Later (after pins): new `Bridge/CookReckhow.lean` (not yet present)
- Gate: `lake build` + `scripts/check_axioms.sh`
- No auto-loop until both pins close

## Open Frontier pins

- `truthTable_is_prop_proof_system` (~3707) —
  `Nonempty (IsPropProofSystem truthTableProofSystem)`
- `validatesTautologyResult_computableInPolyTime` (~6102) —
  needs formula `evalOn` FinTM2, index-loop sequencer, TT map glue

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
- [ ] Glue decode-pair → decode-formula → length gate → loop →
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
  Remaining: leftover true drain, general pair-parse fail, and width
  mismatch zipper (`adr_evals_eq_pow2_ne` / `adr_evals_mvParse_width_ne`)
  are certified; still need decode-formula fail, eval-false, then package
  `afterDecodePairResultComputableInPolyTime`)
- [ ] Package
  `TM2ComputableInPolyTime idBitEnc idBitEnc validatesTautologyResult_on_pair`
  (local composition; no mathlib `.comp`)
- [ ] Remove sorry; commit

### B. Soft pin — `truthTable_is_prop_proof_system` (~3707)

- [ ] Derive TT-map poly witness from A (or thin wrapper over
  `validatesTautologyResult_on_pair` + seed emits)
- [ ] Package
  `⟨{ poly := …, sound := truthTableProofSystem_sound,
  complete := truthTableProofSystem_complete }⟩`
- [ ] Confirm `truthTable_not_poly_bounded` still green
- [ ] Remove sorry; commit

### C. R5 finish (after A+B)

- [ ] Add `CookReckhow.lean`: bridge theorems 1–2 + summit corollary from
  pinned Complexity + ProofSystem
- [ ] Wire into `Theory.lean`; axiom gate PASS; zero Bridge sorries
- [ ] Update rung memory; mark R5 certified
- [ ] Only then consider `satday auto` again

## Order rule

A → B → C. Soft pin is blocked on A's poly witness. One micro-lemma commit
at a time; refuse drafts that cite unknown identifiers.
