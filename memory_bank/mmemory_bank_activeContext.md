# Active Context: Current Focus and Next Steps

## Last Updated: 2026-03-04 (Session 7 - Stage 2: V11/V12/V13/V14)

## Current Status: Phase 6 Active (V11 COMPLETE, V12 scaffold COMPLETE, V13 COMPLETE, V14 partial)

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

## What Is Missing (Next Steps After Session 7)

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

## Git Commits (Sessions 5-7)

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
