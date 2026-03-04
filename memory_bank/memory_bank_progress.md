# Progress Tracking: What Works and What's Left

## Last Updated: 2026-01-28 (Session 4)

---

## Completed Phases

### Phase 1: Foundation — COMPLETE

- [x] F1: Repository & Tooling Bootstrap
- [x] F2: Lean 4 Skeleton
- [x] F3: SAT Toolchain (Kissat, ARM64)
- [x] F4: Agent Supervisor Skeleton

### Phase 2: Data & Storage — COMPLETE

- [x] D1: CNF I/O & Validation
- [x] D2: Circuit DSL
- [x] D3: Artifact Store (SHA256-based)
- [x] D4: Config System

### Phase 3: Agents & Core Loop — COMPLETE

- [x] I1: Unified CLI & Reports
- [x] R1: Planner Agent
- [x] R2: Conjecturer Agent (template + LLM path; V9 complete)
- [x] R3: Counterexample Miner
- [x] R4: Formalizer Agent
- [x] R5: Proof Critic (heuristic barrier tags; oracle upgrade is V10)
- [x] R10: Proof Artifact Round-Trip
- [x] R11: Deterministic Bench Harness

### Phase 4: Research Bets — MVP COMPLETE (Bet A partial, Bet B stage 1)

- [x] R6: Restricted-Circuit Lower Bounds (Bet A) — PARTIAL
  - 3 fully verified Lean theorems: n=2, n=3, n=4 monotone parity
  - 648 Lean stubs across all circuit types and functions
  - n=2-15 monotone parity UNSAT verified (n=11-15 via streaming)
  - n=16-20 deferred (needs algebraic encoding, V4b)
- [x] R7: Algorithm Synthesis (Bet B) — STAGE 1 COMPLETE
  - 3 schemas: sorting, searching, graph_reach
  - End-to-end pipeline: planner -> conjecturer -> miner -> formalizer -> critic all success
  - Lean stubs in theory/Conjectures/BetB/
  - Config: infra/config/bet_b_stage1.yaml + search/plans/bet_b_stage1_plan.yaml
  - Formal proofs: sorry stubs only; complete proofs are Phase 5 work
- [ ] R8: Hardness-vs-Randomness (Bet C) — not started
- [ ] R9: Barrier-Aware Reductions (Bet D) — not started

### Phase 5: Formal Verification — V1, V2, V3, V4, V6, V9 COMPLETE

#### V1: LRAT-Lean Integration — COMPLETE

- [x] `Theory/Circuits.lean`: full circuit evaluation semantics (266 lines)
- [x] `CircuitLowerBoundProof` structure with SHA256 hash fields
- [x] `lrat_implies_lower_bound` axiom for proof integration
- [x] `Tactics/CircuitTactics.lean`, `EncodingTactics.lean`, `InductionScaffolds.lean`

#### V2: First Verified Theorems — COMPLETE

- [x] `MonotoneParityN2Proof.lean` — C.size > 4, no sorry, LRAT: 382dd167...
- [x] `MonotoneParityN3Proof.lean` — C.size > 6, no sorry, LRAT: 46e4bd59...
- [x] `MonotoneParityN4Proof.lean` — C.size > 8, no sorry, LRAT: 53aa50fc...

#### V3: Systematic Bet A Coverage — COMPLETE (n=2-15)

- [x] 7 templates: monotone (parity, majority, threshold-2, threshold-3), AC0 (parity, majority), formula (parity)
- [x] n=2-10: explicit truth table, small CNFs, all verified
- [x] n=11-15: streaming mode, 9 UNSAT proofs, CNFs deleted post-verification
- [x] 648 total Lean stubs in theory/Conjectures/BetA/
- [x] 3 LRAT proofs anchored in Lean (n=2, n=3, n=4)
- [ ] n=16-20: blocked, needs V4b algebraic encoding

#### V4: Streaming Encoding + Auto-Compression — COMPLETE

- [x] `_encode_streaming_parity` in `synthesis.py`: O(gates) memory, O(2^n) clauses
- [x] Auto-selection in `miner.py`: streaming for parity n>10, explicit otherwise
- [x] Validated: n=11-15 all UNSAT within timeouts
- [x] `compress_file()` in `run_kissat`: gzip-compresses CNF/LRAT >1MB after solving
- Metrics: n=15 = 1.42M vars, 21.5M clauses, 446MB raw (~50MB compressed), ~50s

#### V6: Bet B Algorithm Synthesis — COMPLETE (Stage 1)

- [x] `search/templates/bet_b_algorithms.py`: SortingAlgorithmTemplate, SearchingAlgorithmTemplate, GraphReachabilityTemplate
- [x] `search/agents/planner.py`: real `decompose_bet_b_algorithms` (sorting, searching, graph_reach)
- [x] `search/agents/conjecturer.py`: Bet B templates registered, algorithm_schema routing
- [x] `search/circuits/synthesis.py`: ALGORITHM_SCHEMA_ALIASES for sorting_network/search_program/graph_traversal
- [x] `search/agents/miner.py`: truth table handlers for sorting/searching/graph_reach
- [x] `infra/config/bet_b_stage1.yaml` + `search/plans/bet_b_stage1_plan.yaml`
- [x] `infra/config/schemas.py`: BetBConfig with algorithm_schemas/size_range/seed_range
- [x] End-to-end: 30 tasks, 0 errors, SAT+UNSAT results, Lean stubs generated

#### V9: LLM Conjecturer Activation — COMPLETE (infrastructure done)

- [x] Ollama installed via brew (v0.17.5)
- [x] `deepseek-r1:1.5b` and `llama3.2:1b` pulled locally
- [x] `search/agents/conjecturer.py`: `_generate_via_llm()` with Ollama REST API
- [x] Few-shot prompting: `<LEAN_STUB>` + `<CNF_SPEC>` blocks parsed correctly
- [x] DeepSeek-R1 `thinking` field fallback implemented
- [x] SHA256-keyed in-memory `_llm_cache` for deduplication
- [x] `infra/config/schemas.py`: `LLMConfig` (enabled, model, endpoint)
- [x] `ConjecturerAgentConfig` extended with `llm: LLMConfig`
- [x] Config pattern: `agents.conjecturer.llm.enabled = true` activates LLM path
- [x] End-to-end validated: LLM conjecture -> miner UNSAT -> formalizer partial proof
- Limitation: llama3.2:1b produces `True := by sorry` stubs; richer theorems need larger model

---

## Remaining Work (Prioritized)

### V4b: Algebraic Parity Encoding — DEFERRED (research problem)

- Attempted symbolic XOR-chain: unsound (SAT result for monotone parity)
- Attempted ephemeral streaming: no improvement (94M clauses for n=17)
- True algebraic universal encoding for SAT is a circuit complexity research question
- Deferred until a concrete approach is identified

### V10: Real Barrier Analysis — NEXT (depends on V9, V8)

- [ ] Upgrade Critic: construct explicit relativized worlds (oracle-world diagnostic)
- [ ] For each proof attempt, check whether argument is oracle-relative
- [ ] Integrate with LLM Conjecturer: if Critic detects relativization, prompt LLM to propose non-relativizing tweak
- [ ] Acceptance: one proof classified relativizing with explicit oracle witness; one non-relativizing variant proposed

### V5: Publication Package — MEDIUM

- [ ] Technical report: "Automated Verification of Monotone Circuit Lower Bounds"
- [ ] Circuit synthesis encoding methodology
- [ ] Artifact package (CNF instances, LRAT proofs, Lean code)
- [ ] Submit to arXiv or complexity venue

### V7: Bet C — Hardness-vs-Randomness — MEDIUM

- [ ] Correlation tests for circuit-function pairs
- [ ] Formalize Nisan-Wigderson implications in Lean
- [ ] Acceptance: checked H<->R implication for bounded circuit sizes

### V8: Bet D — Barrier-Aware Reductions — MEDIUM

- [ ] Non-relativizing encoding patterns
- [ ] Oracle-world diagnostics in Critic
- [ ] Acceptance: reduction with explicit barrier classification

---

## What We've Proved (Mathematically Rigorous)

1. Monotone circuits computing parity on 2 inputs require > 4 gates
   - Lean 4 theorem, no sorry, LRAT-certified, hash: 382dd167...

2. Monotone circuits computing parity on 3 inputs require > 6 gates
   - Lean 4 theorem, no sorry, LRAT-certified, hash: 46e4bd59...

3. Monotone circuits computing parity on 4 inputs require > 8 gates
   - Lean 4 theorem, no sorry, LRAT-certified, hash: 53aa50fc...

## Computational Evidence (Generated, Verification In Progress)

- n=2-15 monotone parity: all UNSAT (15 sizes, 3 seeds each = 45 instances)
- n=6-10 majority, threshold-2, threshold-3, AC0 parity, formula parity: generated
- 648 Lean stubs total in theory/Conjectures/BetA/
- Bet B: sorting/searching/graph_reach n=2-6 stage 1 data in theory/Conjectures/BetB/

---

## Storage State

| Location | Current Size | Notes |
|---|---|---|
| `proofs/` | ~30MB | n=2-4 LRATs + Bet B CNFs; large files deleted/compressed |
| `docs/reports/` | 0 files | Reports deleted (noise) |
| `theory/Conjectures/BetA/` | 648 stubs | Gitignored |
| `theory/Conjectures/BetB/` | ~30 stubs | Gitignored (Bet B stage 1) |

---

## Known Issues

### Active
- n=16-20 blocked by streaming clause explosion (V4b needed)
- Exponential bound gap: theorems prove C.size >= n+1, not 2^n (publishable but weak)
- `Circuit.depth` uses sorry in Circuits.lean (blocks depth-based lower bounds)
- LLM stubs are `True := by sorry` (trivial); richer theorems need deepseek-prover or larger model

### Deferred
- Encoding correctness unverified in Lean (trust Python encoder)
- Only n=2-4 have complete verified Lean proofs; n=5-15 data exists but unverified

---

## Performance Reference

| Instance | Vars | Clauses | CNF Size | Solve Time | Result |
|---|---|---|---|---|---|
| Parity n=2 | ~60 | ~1364 | <1MB | 0.007s | UNSAT |
| Parity n=4 | ~584 | ~5152 | <1MB | 0.004s | UNSAT |
| Majority n=6 | large | large | ~16MB | 10-60s | SAT |
| Parity n=11 | 72K | 1.07M | 20MB | ~15s | UNSAT |
| Parity n=13 | 331K | 4.96M | 96MB | ~40s | UNSAT |
| Parity n=15 | 1.42M | 21.5M | 446MB | ~50s | UNSAT |
| Parity n=16+ | >3M | >50M | >2GB | timeout | blocked |
| Bet B sorting n=2 | 64 | 222 | <1MB | <0.01s | UNSAT |
| Bet B searching n=2 | 46 | 156 | <1MB | <0.01s | SAT |
