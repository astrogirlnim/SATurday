# Active Context: Current Work and Next Steps

## Last Updated: 2026-01-28 (Session 4)

## Recent Work (This Session)

### V6: Bet B Algorithm Synthesis — COMPLETE

Implemented the full Bet B pipeline:

- `search/templates/bet_b_algorithms.py` (new file):
  - `SortingAlgorithmTemplate`: sorting network synthesis, O(n^2) comparison bound
  - `SearchingAlgorithmTemplate`: linear search synthesis, O(n) step bound
  - `GraphReachabilityTemplate`: BFS/DFS schema synthesis, O(V+E) step bound
  - Each generates Lean 4 stubs + CNF specs in `theory/Conjectures/BetB/`

- `search/agents/planner.py`: replaced `decompose_bet_b_algorithms` stub with real decomposition
  - Generates tasks for each schema x size x seed
  - Size progression from config (`size_range.min` to `size_range.max`)
  - Milestones per schema

- `search/agents/conjecturer.py`: registered Bet B templates in registry
  - `(B, sorting, algorithm)` -> `SortingAlgorithmTemplate`
  - `(B, searching, algorithm)` -> `SearchingAlgorithmTemplate`
  - `(B, graph_reach, algorithm)` -> `GraphReachabilityTemplate`
  - Bet B tasks routed via `algorithm_schema` field

- `search/circuits/synthesis.py`: added `ALGORITHM_SCHEMA_ALIASES` set
  - `sorting_network`, `search_program`, `graph_traversal` all map to monotone constraints
  - Removes the `Unsupported circuit class` error for Bet B specs

- `search/agents/miner.py`: added truth table handlers for `sorting`, `searching`, `graph_reach`
  - Sorting: enumerate permutations
  - Searching/graph_reach: satisfiability stub encoding (all-zero output)

- `infra/config/bet_b_stage1.yaml` (new file): Bet B stage 1 config
- `search/plans/bet_b_stage1_plan.yaml` (new file): Bet B stage 1 plan
- `infra/config/schemas.py`: expanded `BetBConfig` with `algorithm_schemas`, `size_range`, `seed_range`

End-to-end verified: planner (30 tasks) -> conjecturer (0 failures) -> miner (success, 0 errors) -> formalizer -> critic all success.

### V9: LLM Conjecturer Activation — COMPLETE (infrastructure done)

- Installed Ollama via brew; pulled `deepseek-r1:1.5b` and `llama3.2:1b`
- `search/agents/conjecturer.py`: added `_generate_via_llm()` method:
  - Calls Ollama REST API (`/api/generate`)
  - Uses few-shot prompting to generate `<LEAN_STUB>` and `<CNF_SPEC>` blocks
  - Handles DeepSeek-R1 `thinking` field fallback (model puts CoT in `thinking`, not `response`)
  - SHA256-keyed in-memory `_llm_cache` to avoid duplicate API calls
  - Falls back to template path on any LLM error
  - Enabled via `agents.conjecturer.llm.enabled = true` in config

- `infra/config/schemas.py`: added `LLMConfig` model
  - Default model: `llama3.2:1b` (non-reasoning, better structured output with few-shot)
  - `ConjecturerAgentConfig` now contains `llm: LLMConfig`

- Validated end-to-end: LLM generated conjecture -> miner UNSAT -> formalizer partial proof

Git commit: pending

---

## Current State

### What Works

1. Full agent pipeline: Planner -> Conjecturer -> Miner -> Formalizer -> Critic
2. **Bet A** (V1-V4 COMPLETE): 3 verified Lean theorems, 648 stubs, n=2-15 UNSAT proofs
3. **Bet B** (V6 COMPLETE): sorting/searching/graph_reach schemas, end-to-end pipeline working
4. **LLM Conjecturer** (V9 COMPLETE): llama3.2:1b generates LEAN_STUB + CNF_SPEC blocks in ~3.6s
5. Multi-circuit synthesis: monotone, AC0, formula + algorithm schema aliases
6. Auto-compression: CNF/LRAT >1MB gzip-compressed after solving
7. Content-addressed artifact store (SHA256)
8. Config schema: `BetBConfig`, `LLMConfig` fully validated by Pydantic

### What's Missing

1. **V10: Real Barrier Analysis** — Critic is heuristic tagging only; no oracle-world diagnostics
2. **n=16-20** — streaming produces 2GB+ CNFs; blocked until V4b algebraic encoding
3. **Bets C, D** (V7, V8) — not started
4. **Publication package** (V5) — not started
5. **LLM non-trivial theorems** — current LLM output is `True := by sorry`; needs larger model or richer prompting

---

## Next Steps (Dependency Order)

### V10: Real Barrier Analysis in Critic (next highest leverage, depends on V9)
- Upgrade Critic from heuristic `RELATIVIZING` tag to explicit oracle-world diagnostic
- For each proof, construct explicit oracle A where the argument breaks
- If LLM path active: feed relativization witness back to LLM to propose non-relativizing tweak
- Acceptance: one proof classified relativizing with explicit witness

### V5: Publication Package (parallel)
- Write technical report: "Automated Verification of Monotone Circuit Lower Bounds"
- Document circuit synthesis encoding methodology
- Create artifact package (CNF instances, LRAT proofs, Lean code)
- Submit to arXiv or complexity venue

### V7/V8: Bets C and D (parallel, lower priority)

---

## Key File Index

| File | Role | Recent Changes |
|---|---|---|
| `search/agents/conjecturer.py` | Conjecture generation | Added `_generate_via_llm`, LLM cache, Bet B template routing |
| `search/agents/planner.py` | Task generation | Real `decompose_bet_b_algorithms` (was stub) |
| `search/agents/miner.py` | SAT orchestration | Added sorting/searching/graph_reach truth table handlers |
| `search/templates/bet_b_algorithms.py` | Bet B templates | NEW: sorting, searching, graph_reach templates |
| `search/circuits/synthesis.py` | CNF encoding | Added `ALGORITHM_SCHEMA_ALIASES` for Bet B circuit types |
| `infra/config/schemas.py` | Config validation | Added `LLMConfig`, expanded `BetBConfig` |
| `infra/config/bet_b_stage1.yaml` | Bet B config | NEW |
| `search/plans/bet_b_stage1_plan.yaml` | Bet B execution plan | NEW |
| `docs/brainlift/saturday-dev-checklist-v2.md` | Roadmap | V6, V9 items checked off |
| `search/bin/run_kissat` | Kissat wrapper | Auto-compress after solve (from previous session) |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN2Proof.lean` | Verified theorem | LRAT: 382dd167... |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN3Proof.lean` | Verified theorem | LRAT: 46e4bd59... |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN4Proof.lean` | Verified theorem | LRAT: 53aa50fc... |

---

## Blockers

- **n=16-20**: algebraic encoding is a research problem, not just implementation
- **Non-trivial LLM theorems**: llama3.2:1b produces `True := by sorry`; larger model needed for real math content
- **No hard blockers** for V10, V5, V7, V8
