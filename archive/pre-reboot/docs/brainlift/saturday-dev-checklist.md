MVP Development Checklist — **SATurday (Zero-Cost, Local-Only Edition)**

Template Overview
This checklist provides a structured approach to implementing SATurday entirely on a local MacBook Pro (M4), with zero cloud spend and no paid APIs. Each phase represents a milestone; features within a phase are independently implementable and testable in isolation.

Phases Overview
[ ] Phase 1: Foundation
[ ] Phase 2: Data Layer
[ ] Phase 3: Interface Layer
[ ] Phase 4: Implementation Layer

---

### Phase 1

**Criteria:** Essential systems the application cannot function without. These are the building blocks for all other functionality.

[ ] **F1. Repository & Tooling Bootstrap (independent – no dependencies)**
[ ] Create a monorepo with top-level folders `theory/`, `search/`, `proofs/`, `infra/`, and `docs/`.
[ ] Add a `LICENSE` (MIT), `README.md`, `CONTRIBUTING.md`, and `CODE_OF_CONDUCT.md`.
[ ] Provide a `Makefile` with targets: `setup`, `build`, `test`, `verify`, `bench`, `check-proofs`, and `publish`.
[ ] Add a `.editorconfig` and reasonable `.gitignore` entries for Lean, Python, and build artifacts.
[ ] Acceptance: Cloning the repo and running `make setup` completes without errors and creates all folders/files.

[ ] **F2. Local Environment Setup (independent – no dependencies)**
[ ] Write a script `infra/scripts/bootstrap_macos.sh` that installs Homebrew if missing and installs Lean 4, Python 3.12+, cmake, ninja, gcc-llvm, and required SAT solver build tools.
[ ] Provide a `uv` (or `pipx` + `venv`) Python environment bootstrap with a pinned `pyproject.toml` for ARM64 macOS.
[ ] Add pre-commit hooks for black/ruff (Python) and a Lean formatter (e.g., `lake fmt` alias).
[ ] Acceptance: `make setup` creates a Python venv, enables pre-commit, and verifies all tool versions locally.

[ ] **F3. Lean 4 Project Skeleton (independent – no dependencies)**
[ ] Initialize a Lean 4 project in `theory/` with `lakefile.lean`, `lean-toolchain`, and `Theory/` module namespace.
[ ] Add `mathlib` as a dependency and confirm compilation on M4.
[ ] Provide minimal example: a small lemma with a unit test using `lake build` / `lake test`.
[ ] Acceptance: `make verify` builds Lean project successfully and runs the sample test.

[ ] **F4. SAT Toolchain (independent – no dependencies)**
[ ] Add `infra/build/kissat_build.sh` to compile Kissat locally (ARM64 flags) with no network beyond the initial git submodule.
[ ] Vendor or submodule a stable version of CaDiCaL or Kissat; store patches in `infra/patches/`.
[ ] Provide a `search/bin/run_kissat` wrapper that enforces CPU-only, fixed seeds, and outputs DRAT/LRAT logs.
[ ] Acceptance: Running `search/bin/run_kissat examples/mini.cnf` returns SAT/UNSAT with a proof log in `proofs/`.

[ ] **F5. Zero-Cost Guard & Offline Policy (independent – no dependencies)**
[ ] Implement `infra/policy/zero_cost_guard.py` that fails the build if any API keys are detected in env, config, or git history.
[ ] Add a policy file `infra/policy/OFFLINE_ONLY.md` describing the prohibition of outbound network calls during runs.
[ ] Wire `zero_cost_guard.py` into `make verify` to block accidental paid/API usage.
[ ] Acceptance: Builds fail if any outbound API dependency or key is detected.

[ ] **F6. Minimal Agent Supervisor Skeleton (independent – no dependencies)**
[ ] Create `search/agents/supervisor.py` that loads a YAML plan, spawns agent steps in sequence, and writes logs to `search/logs/`.
[ ] Define agent interfaces (`AgentBase` with `plan()`, `act()`, `report()`) in `search/agents/core.py`.
[ ] Provide stub agents: `planner.py`, `conjecturer.py` (no LLM yet), `miner.py`, `formalizer.py`, `critic.py`.
[ ] Acceptance: `make test` runs a dry cycle where each agent writes a stub report without external calls.

[ ] **F7. Testing & CI-Local (independent – no dependencies)**
[ ] Add pytest with a local test suite for Python and a Lean test target; no online CI, only `make test`.
[ ] Provide snapshot tests for the supervisor’s logs to ensure reproducible ordering and content.
[ ] Acceptance: `make test` passes locally; removing any component causes clear test failures.

---

### Phase 2

**Criteria:** Systems for storing, retrieving, and managing application data. Each feature handles a specific data or storage mechanism and depends on Phase 1.

[ ] **D1. CNF/Dimacs I/O & Validation (depends on Phase 1)**
[ ] Implement `search/io/cnf_reader.py` to parse DIMACS and validate headers, clause counts, and variable ranges.
[ ] Implement `search/io/cnf_writer.py` to emit normalized DIMACS with stable variable ordering.
[ ] Add unit tests with malformed and well-formed fixtures in `search/tests/data/`.
[ ] Acceptance: Round-trip parse→write preserves semantics; validators catch malformed inputs.

[ ] **D2. Circuit DSL (depends on Phase 1)**
[ ] Implement `search/circuits/dsl.py` for monotone/formula/AC⁰ fragments with constructors for gates, depth, and fan-in.
[ ] Implement `search/circuits/to_cnf.py` to encode candidate circuits as CNF for small n.
[ ] Provide invariants checkers (acyclicity, size limits) and export graphs for inspection.
[ ] Acceptance: Unit tests generate tiny circuits and produce CNF encodings that solve with Kissat.

[ ] **D3. Artifact Store (depends on Phase 1)**
[ ] Create a content-addressed store in `proofs/` using SHA256 for DRAT/LRAT, CNF inputs, and solver configs.
[ ] Implement `search/storage/index.json` to record metadata (timestamp, solver, seed, hash links).
[ ] Provide `search/tools/inspect_artifacts.py` to query by hash or tag.
[ ] Acceptance: Creating a new proof log registers a unique hash; re-runs with same inputs yield identical hashes.

[ ] **D4. Config System (depends on Phase 1)**
[ ] Implement `infra/config/defaults.yaml` and `infra/config/schemas.py` using `pydantic` for validation.
[ ] Provide `--config` override and environment variable overrides in the supervisor.
[ ] Acceptance: Invalid config keys fail with actionable error messages; valid configs load deterministically.

---

### Phase 3

**Criteria:** User-facing components and interactions (CLI/TUI and developer ergonomics). Depends on Phases 1 & 2.

[ ] **I1. Unified CLI (depends on Phase 1 & 2)**
[ ] Implement `satday` CLI (via `typer`) with commands: `satday mine`, `satday bench`, `satday check-proofs`, `satday verify`.
[ ] Provide `--offline` flag that enforces zero-network mode and blocks any subprocess that attempts sockets.
[ ] Acceptance: Each command executes end-to-end local workflows and writes outputs to deterministic locations.

[ ] **I2. Reports & Logs (depends on Phase 1 & 2)**
[ ] Implement `search/reporting/md_reporter.py` to render run summaries to Markdown in `docs/reports/`.
[ ] Add per-agent logs with stable JSONL entries for easy diffing; include start/stop times and deterministic seeds.
[ ] Acceptance: Running any cycle produces a human-readable report and a machine-readable JSONL log.

[ ] **I3. Local Docs Build (depends on Phase 1 & 2)**
[ ] Add a local `mkdocs` (or `mdBook`) site with an offline theme; no CDN fonts, all assets vendored.
[ ] Generate API docs for Python and Lean symbols where possible; link to examples.
[ ] Acceptance: `make publish` builds a static site under `docs/site/` entirely offline.

[ ] **I4. Minimal TUI (optional) (depends on Phase 1 & 2)**
[ ] Implement a textual TUI (`textual`/`rich`) that shows queue status of agents, last run verdicts, and artifact counts.
[ ] Provide keyboard shortcuts to open the latest Markdown report and artifact folder.
[ ] Acceptance: Launching the TUI displays real-time progress from log tailing without network calls.

---

### Phase 4

**Criteria:** Main application functionality and research capabilities. Depends on Phases 1, 2 & 3.

[ ] **R1. Planner Agent v1 (depends on Phase 1, 2 & 3)**
[ ] Implement rule-based decomposition for four research bets (Restricted Lower Bounds, Algorithm Synthesis, H↔R, Barrier-Aware Reductions).
[ ] Provide a YAML plan format specifying tasks, seeds, size ranges, and acceptance thresholds.
[ ] Acceptance: Given a plan, the supervisor schedules tasks and records a completed plan run with all steps logged.

[ ] **R2. Conjecturer Agent v1 (Zero-Cost Mode) (depends on Phase 1, 2 & 3)**
[ ] Implement a template-based conjecture generator that mutates circuit parameters and reduction schemas without external LLMs.
[ ] Provide grammar-driven generation (e.g., `lark`) for producing Lean lemma stubs and CNF experiment specs.
[ ] Acceptance: For each template, the agent emits (a) a Lean stub in `theory/Conjectures/` and (b) a CNF spec in `search/specs/`.

[ ] **R3. Counterexample Miner v1 (depends on Phase 1, 2 & 3)**
[ ] Implement CNF synthesis for conjectures and run Kissat with fixed seeds across small n; capture DRAT/LRAT logs.
[ ] Implement structural pattern extraction (e.g., clause distribution, unit propagation statistics) from solver traces.
[ ] Acceptance: For each conjecture, the agent either emits a counterexample artifact or raises confidence with attached logs and stats.

[ ] **R4. Formalizer Agent v1 (Lean 4) (depends on Phase 1, 2 & 3)**
[ ] Implement a Lean tactic script library for routine steps (induction scaffolds, circuit size monotonicity, encoding lemmas).
[ ] Convert successful templates into parameterized Lean theorems with proofs or `sorry` placeholders plus TODOs.
[ ] Acceptance: `make verify` confirms all completed lemmas compile; incomplete items are isolated and marked.

[ ] **R5. Proof Critic v1 (Barrier-Aware Checks) (depends on Phase 1, 2 & 3)**
[ ] Implement a static analyzer that tags proofs as “likely relativizing” or “likely natural” using rule sets and heuristics.
[ ] Provide oracle-world diagnostics for small synthetic oracles and report whether arguments persist or fail.
[ ] Acceptance: Reports include barrier tags with rationale and links to the exact proof fragments or transformations.

[ ] **R6. Restricted-Circuit Lower Bounds Track (Bet A) (depends on R2, R3, R4)**
[ ] Implement monotone and simple formula classes with size/depth constraints and prove baseline lower bounds in Lean.
[ ] Extend to AC⁰ fragments; encode families to CNF for small n and mine patterns that inform general lower-bound lemmas.
[ ] Acceptance: At least one new formally proved lower bound (even restricted) with a reproducible artifact bundle.

[ ] **R7. Algorithm Synthesis with Proven Bounds (Bet B) (depends on R2, R4)**
[ ] Implement schema search over branching rules and decomposition; generate recurrence relations automatically from code.
[ ] Prove upper bounds for selected schemas in Lean via induction or amortized analysis; restrict to promised instances.
[ ] Acceptance: At least one algorithm schema with a Lean-proved polynomial bound on a non-trivial promised class.

[ ] **R8. Hardness-vs-Randomness Workbench (Bet C) (depends on R2, R3, R4)**
[ ] Implement correlation tests between tiny explicit functions and small circuit ensembles; export data tables.
[ ] Formalize micro-implications in Lean linking correlation bounds to PRG sketches for toy parameters.
[ ] Acceptance: A Lean-checked implication connecting a measured correlation bound to a PRG-style statement for bounded sizes.

[ ] **R9. Barrier-Aware Reductions (Bet D) (depends on R2, R4, R5)**
[ ] Implement non-relativizing encodings using simple arithmetization steps and interactive-proof-style gadgets for toy settings.
[ ] Provide oracle diagnostics that demonstrate the argument fails under certain oracles (signal: non-relativizing tendencies).
[ ] Acceptance: A documented reduction with barrier diagnostics and a partial Lean proof of its critical invariants.

[ ] **R10. Proof Artifact Round-Trip (depends on R3, R4)**
[ ] Implement a converter that references LRAT-verified solver logs inside Lean lemmas as external certificates (hash-anchored).
[ ] Provide a `make check-proofs` target that replays LRAT checks and ensures Lean references match file hashes.
[ ] Acceptance: Breaking a proof log hash causes `make check-proofs` to fail; fixing it restores green.

[ ] **R11. Deterministic Bench Harness (depends on Phase 1, 2 & 3)**
[ ] Implement a seed/stress matrix runner for small CNFs that enforces fixed CPU affinity and consistent timing.
[ ] Export Markdown and CSV summaries for inclusion in `docs/reports/` with reproducible numbers.
[ ] Acceptance: Repeated runs on the same machine produce identical results within tight variance bounds.

[ ] **R12. Offline Local “LLM” Option (optional, zero-cost) (depends on Phase 1, 2 & 3)**
[ ] Integrate a tiny local inference path (e.g., grammars + beam search or an embedded small open-weights model via llama.cpp) guarded by the offline policy.
[ ] Cache prompts/outputs to disk to ensure deterministic regeneration.
[ ] Acceptance: Conjecturer can switch between template-only and local model modes with identical file outputs for the same seed.

---

### Implementation Guidelines

**Phase Criteria Definitions**
Phase 1: Must be completed first; features are independent and unblock later phases.
Phase 2: Begins after Phase 1; focuses purely on data handling.
Phase 3: Begins after Phase 1; focuses on CLI/TUI and reporting.
Phase 4: Begins after Phases 1–3; implements research capabilities and agents.

**Feature Independence Rules**

* **Zero Dependencies:** Each sub-feature is implementable without requiring other sub-features first.
* **Self Contained:** Each sub-feature includes all components to function independently.
* **Testable in Isolation:** Each sub-feature has explicit acceptance criteria.
* **Rollback Safe:** Each sub-feature can be disabled or removed without breaking other functionality.

**Priority Classification**

* **Critical Importance:** F1–F4, F6, D1–D4, I1, R1–R5, R10
* **High Importance:** I2–I3, R6–R9, R11
* **Medium Importance:** F5, I4
* **Nice to Have:** R12

**Status Tracking**
[ ] Not Started [x] Completed [~] In Progress [!] Blocked

