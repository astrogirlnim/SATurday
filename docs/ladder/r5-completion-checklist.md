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
  length-count Stmt labels (`lenLoop`/`lenInc`/`lenRestore`/`lenFinish`)
  and step lemmas present (entry still stub via `clearLeft`);
  Remaining: wire `allTrueOk` → `lenLoop`, pow2 compare, indexValidate
  under `|table|` fuel → `acceptEmit`; package
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
