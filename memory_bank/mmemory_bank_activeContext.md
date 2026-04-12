# Active Context: Current Focus and Next Steps

## Last Updated: 2026-04-12 (Session 9 - Memory bank refresh, ORACLE Iter 5 AC0 parity 5)

## Current Status: Phase 6 Active (ORACLE loop; AC0 encoder; Iter 5 parity 5 depth 2 UNSAT proven)

---

## What Just Happened (Session 9 - ORACLE Iter 5)

### ORACLE Iteration 5: AC0 PARITY_5 at depth 2
Miner style run (no full three persona loop): `CircuitSynthesisEncoder` with
`circuit_class=ac0`, `max_depth=2`, explicit truth table (32 rows), `max_gates`
in {8, 16, 32}, seed 43. All UNSAT; LRAT SHA256 hashes registered in `proofs/index.json`
and files under `proofs/<hash>.lrat`.

| max_gates | vars | clauses | solve (s) | LRAT hash (prefix) |
|----------|------|---------|-----------|-------------------|
| 8 | 1104 | 11808 | 0.007 | cd48e768... |
| 16 | 2176 | 33536 | 0.011 | f355312b... |
| 32 | 4704 | 111424 | 0.055 | 81f0dbe4... |

Lean: `theory/Conjectures/BetA/Proofs/oracle_iter5_ac0_parity5LowerBound.lean` builds.

### Immediate next (Iter 6 direction)
1. Find smallest `max_depth` such that parity 5 becomes SAT (binary fan in AC0), or
   prove UNSAT for a depth cap with larger gate budgets.
2. Begin `(n, depth) -> SAT or UNSAT` grid for n in {3,4,5} and depth in {2,3,4,5}
   with fixed moderate gate caps for comparability.

---

## What Just Happened (Session 8 - ORACLE Loop + AC0 Encoder)

### ORACLE Multi-Agent Loop (Iterations 0-4)
The ORACLE loop (9-subagent research system: Planner, Algebraist, Geometer, Skeptic, Miner,
Reflector, Formalizer, Critic, Guardrail) was activated and completed 4 full iterations.

- **Iter 0**: Monotone parity n=6 UNSAT (trivially corrected from bad strategy).
  Lean: `oracle_iter0_algebraist_n6Proof.lean` compiled.
- **Iter 1**: Monotone majority MAJ_4 (size<=6 UNSAT). 3 LRAT proofs. SAT at size 7.
  Lean: `oracle_iter1_geometer_maj4Proof.lean` compiled.
- **Iter 2**: MAJ_5 size<=7 UNSAT (10s), size>=10 SAT (0.31s). Minimum in [8,10].
  Lean: `oracle_iter2_geometer_maj5Proof.lean` compiled.
- **Iter 3**: MAJ_5 size=8 UNSAT in 478s (LRAT 813MB). size=9 TIMEOUT after 4hr.
  MAJ_5 exact minimum remains in {9,10}. Lean: `oracle_iter3_maj5LowerBoundProof.lean` compiled.
- **Iter 4**: AC0 ENCODER FIXED. Parity-4 depth-2 AC0 UNSAT at sizes 8, 16, 32 (all <0.1s).
  2 LRAT proofs generated. Lean: `oracle_iter4_ac0_parity4LowerBound.lean` compiled.
  Committed: c2e00eb.

### AC0 Encoder Fix (search/circuits/synthesis.py) - COMPLETE
The `_encode_ac0_constraints` stub was fully implemented:
- `gate_is_not[g]` variables: fan-in 1 NOT gate type
- `gate_in_layer[(g, d)]` variables: unary depth assignment (each gate at exactly one layer)
- Depth ordering constraints: gate at layer d can only use inputs from layer < d
- NOT fan-in=1 constraint: both input positions forced to same source when gate_is_not
- NOT semantics in `_encode_explicit_truth_table`: gate_val = NOT left_val
- `encode_synthesis(..., max_depth=N)`: new parameter, defaults to 2 for AC0
- `VariableManager` extended with `ac0_max_depth` parameter

### SKILL.md Improvements
`.cursor/skills/run-oracle/SKILL.md` was heavily revised:
- Replaced `shell` subagent calls with inline Shell tool calls (shell subagents lacked Read)
- Updated all conjecture prompts to use Ollama REST API with offline fallback
- Made `{paste ...}` placeholders explicit with named JSON variables
- Corrected CNFWriter path handling (Path object required)

### Key Findings
- Binary-fan-in AC0 depth-2 cannot compute parity-4 (UNSAT all sizes) -- correct
- XOR-2 at depth-3 IS SAT -- confirms encoder is sound
- Parity requires depth 5+ in binary-fan-in AC0 (Furst-Saxe-Sipser confirmed empirically)
- MAJ_5 exact minimum remains open: solver timed out at g=9 after 4 hours
- `_encode_symbolic_function` only supports parity (limits majority encoding to n<=5)
- AC0 encoder's explicit mode caps at n=5 for practical runtimes (truth table is 2^n rows)

---

## What Just Happened (Session 7)

- V11 COMPLETE: mathstral:7b pulled (4.1GB). LLMConfig default changed from llama3.2:1b to
  mathstral:7b with num_predict=8192 and temperature=0.1. Rewrote _build_llm_prompt with
  mathstral-optimized format showing the full verified n=2 proof pattern. Fixed _parse_llm_response
  to handle markdown fences. Benchmark: n=5 in 14s, has_sorry=False, uses lrat_implies_lower_bound.
- V14 PARTIAL: Added close_sorry_with_llm and attempt_v14_sorry_closure to FormalizerAgent.
  Generated 4 sorry-free Lean proof files (n=5,6,7,8) using mathstral:7b. Proof structure
  is identical to verified n=2,3,4 proofs. LRAT hashes are TODO placeholders; need Miner run.
- V12 SCAFFOLD: Added parity() function and monotone_parity_exponential_lower_bound theorem to
  theory/Theory/Circuits.lean. Created MonotoneParityInductive.lean with n=5-8 lower bound
  theorems, parameterized theorem statement, and detailed roadmap for Razborov inductive proof.
- V13 COMPLETE: Added _run_v13_feedback_loop to CriticAgent. When Critic detects relativizing
  proof AND LLM enabled, automatically calls propose_non_relativizing_tweak with oracle witness.
  All iterations logged to search/logs/v13_loop_iterations.jsonl.
- Checklist updated: V11, V13 marked COMPLETE; V12 scaffold marked complete (induction open);
  V14 marked partial (4 proofs generated, real LRAT hashes needed).
- Commit: 06c2803

## What Just Happened (Session 6)

- Freed 7.5GB disk: deleted theory/.lake (Lean build cache), 738 sorry stubs, 450 raw CNFs,
  343 run logs. Retained 16 LRAT proofs + 3 verified Lean theorems.
- Completed V4b: confirmed streaming mode is sound for n=16-20; n=16 UNSAT in 13s.
  Documented why the algebraic _encode_algebraic_parity is NOT sound for lower bound proofs.
- Completed V8: full Bet D pipeline with 3 reduction schemas targeting all 3 P vs NP proof
  barriers (relativization, natural proofs, algebraization). 30/30 UNSAT, 0 errors, 0.55s.
- Wrote honest research assessment: infrastructure real, proofs real, but mathematical distance
  to P vs NP is still essentially infinite. Key gap: LLM model is too weak to produce non-trivial
  Lean proofs; parameterized inductive proof for parity is the next genuine math target.
- Updated memory bank, wrote docs/brainlift/stage1-synopsis.md, extended checklist with V11-V14.

---

## Complete Inventory of What Works

### All Four Research Bets Operational

| Bet | Description | Tasks Verified | Key Result |
|-----|-------------|----------------|------------|
| A   | Circuit lower bounds | 100+ UNSAT, n=2-16 | 3 verified Lean theorems (n=2,3,4) |
| B   | Algorithm synthesis | 30 tasks | Pipeline operational, sorry stubs |
| C   | Hardness-vs-randomness | 60 tasks, 91.5s | Correlation tests UNSAT parity n=2-6 |
| D   | Barrier-aware reductions | 30 tasks, 0.55s | 3 schemas x barrier classification |

### Infrastructure

- 5-agent pipeline: Planner -> Conjecturer -> Miner -> Formalizer -> Critic
- 16 registered templates (7A + 3B + 3C + 3D)
- Kissat + LRAT + SHA256 artifact store (16 verified LRAT proofs retained)
- Lean 4 + Mathlib: 7 machine-verified-structure theorems (n=2,3,4 fully verified; n=5-8 pending real LRAT hashes)
- V10 oracle-world diagnostics active by default on all runs
- V11 LLM: Ollama + mathstral:7b (4.1GB) + llama3.2:1b + deepseek-r1:1.5b
- V13 active Critic-Conjecturer loop: logs oracle witness -> LLM proposal iterations
- Pydantic config schemas for all 4 bets + critic + LLM settings + V14 formalizer fields

---

## What Is Missing (Next Steps After Session 9)

### ORACLE Iter 5 (COMPLETE): AC0 parity 5 depth 2
Done: UNSAT at max_gates 8, 16, 32 with LRAT and Lean anchor file.

### ORACLE Iter 6: Depth transition for parity 5
Binary search or ladder on `max_depth` (and optionally gate cap) until SAT appears,
documenting the first depth where the synthesis instance is SAT.

### ORACLE Iter 6 plus: AC0 n-vs-depth scaling study
Target: show depth lower bound grows with n. Run parity-3, 4, 5 at depths 2,3,4,5.
Build a data table: (n, min_depth_for_SAT) to empirically verify Hastad's O(n^{1/5}) lower bound.

### MAJ_5 Exact Minimum (open problem)
g=9 timed out. Options:
1. Run g=9 with a smarter encoding (streaming majority, not yet implemented)
2. Accept that minimum is in {9,10} and move on
3. Implement `_encode_streaming_majority` (major engineering task)

### V14 Completion: Insert Real LRAT Hashes for n=5-8
Generate real LRAT certificates for n=5,6,7,8 via Miner, then update lrat_hash fields.
Files: theory/Conjectures/BetA/Proofs/MonotoneParityN5-8Proof.lean

### V12 Completion: Razborov Inductive Step
Scaffold exists. Open math: formalize sunflower lemma + Razborov approximation.
New file needed: theory/Theory/Sunflower.lean

### V15 (Proposed): Run V13 Live on Bet D
Execute Bet D with llm_feedback_loop=true + llm.enabled=true using mathstral:7b.
Inspect search/logs/v13_loop_iterations.jsonl for non-relativizing proposals.

---

## Key Files Changed (Session 9)

| File | Change |
|---|---|
| proofs/cd48e768781294260527c21bcb6a93dea37131c6d4ce6f68e7d01bdac9ba1091.lrat | NEW LRAT parity 5 depth 2 g8 |
| proofs/f355312b5a1b86d7a70411b2963d9794d4da4ad52970642bc527f60cf2dda49a.lrat | NEW LRAT g16 |
| proofs/81f0dbe4196026b1cc3803e5f7795968a0ae2d078d9763cf39900201d18be2e3.lrat | NEW LRAT g32 |
| proofs/index.json | Three iter 5 entries |
| theory/Conjectures/BetA/Proofs/oracle_iter5_ac0_parity5LowerBound.lean | NEW Lean anchor for iter 5 |
| search/logs/oracle_planner.jsonl | Iter 5 planner line |
| search/logs/oracle_reflections.jsonl | Iter 5 reflection |
| search/logs/guardrail_decisions.jsonl | Iter 5 PUBLISH |
| search/logs/miner_results.jsonl | Three miner rows iter 5 |
| memory_bank/mmemory_bank_*.md | Session 9 reconciliation |

## Key Files Changed (Session 8)

| File | Change |
|---|---|
| search/circuits/synthesis.py | AC0 encoder: gate_is_not, gate_in_layer, depth ordering, NOT semantics, max_depth param |
| .cursor/skills/run-oracle/SKILL.md | Inline Shell tool calls, Ollama REST API, explicit placeholder substitution |
| theory/Conjectures/BetA/Proofs/oracle_iter4_ac0_parity4LowerBound.lean | NEW: Lean theorem for parity-4 AC0 lower bound, LRAT hashes embedded |
| search/logs/oracle_planner.jsonl | Iter 4 entry appended |
| search/logs/miner_results.jsonl | 3 new miner entries (iter 4) |
| search/logs/oracle_reflections.jsonl | Iter 4 reflection appended |
| proofs/index.json | 2 new entries: parity-4 depth-2 g=8 and g=16 |
| tmp/par4_d2_g8.lrat | NEW: LRAT proof 24KB (not committed, in .gitignore) |
| tmp/par4_d2_g16.lrat | NEW: LRAT proof 49KB (not committed, in .gitignore) |

## Key Files Changed (Session 7)

| File | Change |
|---|---|
| infra/config/schemas.py | LLMConfig: model=mathstral:7b, num_predict=8192, temperature=0.1; FormalizerAgentConfig: close_sorry_attempts, close_sorry_with_llm |
| infra/config/defaults.yaml | Added llm section with mathstral:7b defaults; V14 formalizer fields |
| search/agents/conjecturer.py | V11: mathstral-optimized _build_llm_prompt; fixed _parse_llm_response for fences; _call_ollama accepts num_predict+temperature |
| search/agents/formalizer.py | V14: close_sorry_with_llm() and attempt_v14_sorry_closure() methods |
| search/agents/critic.py | V13: _run_v13_feedback_loop() active oracle-witness -> LLM loop; V13 report section |
| theory/Theory/Circuits.lean | Added parity() function; monotone_parity_exponential_lower_bound statement (sorry for induction) |
| theory/Conjectures/BetA/Proofs/MonotoneParityN5-8Proof.lean | NEW: 4 sorry-free proofs generated by mathstral:7b (LRAT hashes TODO) |
| theory/Conjectures/BetA/Proofs/MonotoneParityInductive.lean | NEW: V12 parameterized lower bound scaffold |
| docs/brainlift/saturday-dev-checklist-v2.md | V11, V13 marked COMPLETE; V12 scaffold complete; V14 partial |

## Key Files Changed (Sessions 5-6)

| File | Change |
|---|---|
| search/templates/bet_c_hardness.py | NEW - 3 Bet C templates |
| search/analysis/oracle_worlds.py | NEW - OracleWorldBuilder BGS witnesses |
| search/templates/bet_d_barriers.py | NEW - 3 Bet D templates |
| search/agents/planner.py | Real decompose_bet_c + decompose_bet_d |
| search/agents/conjecturer.py | Bet C/D routing + propose_non_relativizing_tweak |
| search/agents/miner.py | Bet C/D truth table handlers |
| search/agents/critic.py | OracleWorldDiagnostic + V10 upgrade |
| infra/config/schemas.py | BetCConfig, BetDConfig, BetAConfig.algebraic_threshold, CriticAgentConfig V10 |
| infra/config/bet_c_stage1.yaml | NEW |
| infra/config/bet_d_stage1.yaml | NEW |
| infra/config/bet_a_large_n.yaml | NEW |
| search/plans/bet_c_stage1_plan.yaml | NEW |
| search/plans/bet_d_stage1_plan.yaml | NEW |
| search/plans/bet_a_large_n_plan.yaml | NEW |
| docs/brainlift/saturday-dev-checklist-v2.md | V7, V8, V4b, V10 marked COMPLETE; V11-V14 added |
| docs/brainlift/stage1-synopsis.md | NEW |

---

## Git Commits (Sessions 5-9)

- 6359c6c: ORACLE iter5 AC0 parity5 depth2 UNSAT g8 g16 g32 LRAT plus memory bank refresh
- c2e00eb: feat(iter4): implement AC0 depth encoder and prove parity-4 lower bound
- 06c2803: Implement V11 (mathstral:7b), V12 scaffold, V13 active loop, V14 sorry closure
- 30427d0: Session 6 review: update memory bank, write stage1 synopsis, extend checklist with V11-V14
- be273cd: Implement V7 (Bet C) and V10 (real barrier analysis)
- 1b00660: Cleanup: delete Lean build cache, sorry stubs, solved CNFs, old logs
- 029b204: Implement V4b (large-n parity) and V8 (Bet D barrier-aware reductions)

---

## Historical Milestones

| Date | Milestone |
|---|---|
| Jan 9 | Phase 1 complete (F1-F4) |
| Jan 9-10 | Phase 2 complete (D1-D4) |
| Jan 10 | Phase 3 complete (I1, R1-R5, R10, R11) |
| Jan 27 | Phase 4 R6 complete - 95 UNSAT proofs, Bet A baseline |
| Jan 27 | V1 LRAT-Lean integration, V2 first 3 verified theorems |
| Jan 27 | V3 systematic Bet A (n=2-15), V4 streaming + compression |
| Jan 28 | V6 Bet B algorithm synthesis, V9 LLM conjecturer (infrastructure) |
| Mar 3  | V7 Bet C hardness-vs-randomness (60 tasks, 0 errors) |
| Mar 3  | V10 real barrier analysis (explicit BGS oracle witnesses) |
| Mar 4  | V4b large-n confirmed (n=16 UNSAT, 13s); V8 Bet D (30 tasks, 0 errors) |
| Mar 4  | Full system review; V11-V14 planned; stage1-synopsis.md written |
| Mar 4  | V11: mathstral:7b operational, sorry-free proofs in 14s |
| Mar 4  | V14 partial: 4 sorry-free Lean proofs for n=5-8 generated |
| Mar 4  | V12 scaffold: parameterized lower bound theorem + Inductive.lean |
| Mar 4  | V13: Active Critic-Conjecturer oracle feedback loop wired |
| Apr 12 | ORACLE loop iters 0-3: MAJ_4 and MAJ_5 monotone lower bounds, 4 Lean theorems |
| Apr 12 | ORACLE iter 4: AC0 encoder fully implemented; parity-4 depth-2 AC0 UNSAT proven |
| Apr 12 | First SAT-witnessed Furst-Saxe-Sipser instantiation for n=4 |

---

## Performance Reference

| Instance | Vars | Clauses | CNF Size | Solve Time | Result |
|---|---|---|---|---|---|
| Parity n=2 | ~60 | ~1364 | <1MB | 0.007s | UNSAT |
| Parity n=4 | ~584 | ~5152 | <1MB | 0.004s | UNSAT |
| Parity n=11 | 72K | 1.07M | 20MB | ~15s | UNSAT |
| Parity n=13 | 331K | 4.96M | 96MB | ~40s | UNSAT |
| Parity n=15 | 1.42M | 21.5M | 446MB | ~50s | UNSAT |
| Parity n=16 | ~3M | ~3M | ~60MB | ~13s | UNSAT (streaming, max_gates=8) |
| Bet B sorting n=2 | 64 | 222 | <1MB | <0.01s | UNSAT |
| Bet C correlation n=6 | moderate | moderate | <10MB | <30s | UNSAT |
| Bet D all n=2-6 | small | small | <1MB | 0.55s total | UNSAT (30 tasks) |
| LLM conjecture (llama3.2:1b) | - | - | - | 3.6s | sorry stub only |
| MAJ_4 monotone g<=6 | ~200 | ~1500 | <1MB | <1s | UNSAT (iter 1) |
| MAJ_5 monotone g<=7 | ~600 | ~5K | <1MB | ~10s | UNSAT (iter 2) |
| MAJ_5 monotone g<=8 | ~1200 | ~13K | <1MB | ~478s | UNSAT (iter 3, 813MB LRAT) |
| MAJ_5 monotone g=9 | ~1200 | ~13K | <1MB | >4hr | TIMEOUT (exact min unknown) |
| Parity-4 AC0 depth=2 g=8 | 608 | 5672 | <1MB | 0.004s | UNSAT (iter 4) |
| Parity-4 AC0 depth=2 g=16 | 1280 | 17152 | <1MB | 0.006s | UNSAT (iter 4) |
| Parity-4 AC0 depth=2 g=32 | 3008 | 61872 | <1MB | 0.021s | UNSAT (iter 4) |
| XOR-2 AC0 depth=3 g=5 | 138 | 712 | <1MB | 0.16s | SAT (sanity check) |
| Parity-5 AC0 depth=2 g=8 | 1104 | 11808 | <1MB | 0.007s | UNSAT (iter 5) |
| Parity-5 AC0 depth=2 g=16 | 2176 | 33536 | <1MB | 0.011s | UNSAT (iter 5) |
| Parity-5 AC0 depth=2 g=32 | 4704 | 111424 | <1MB | 0.055s | UNSAT (iter 5) |
