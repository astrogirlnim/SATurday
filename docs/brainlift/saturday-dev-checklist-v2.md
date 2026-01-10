### MVP Checklist

To streamline for a simple MVP, I rewrote it: Reduced to ~25 items by merging redundancies (e.g., combined infra bootstraps, unified CLI/reporting), cut medium/nice-to-haves (F5, I3, I4, R12), made phases more flexible (looser dependencies), and prioritized core agent loop + one bet (A: circuit bounds) for quick wins. Focus: Get a verifiable cycle running locally, producing a tiny proved artifact. Add others iteratively. Retained local-only, testability, and ARM64 notes.

**MVP Development Checklist — SATurday (Zero-Cost, Local-Only Edition)**

**Phases Overview**  
[x] Phase 1: Foundation (Core setup; independent)  
[x] Phase 2: Data & Storage (Handles inputs/outputs; depends on Phase 1)  
[ ] Phase 3: Agents & Core Loop (Implements research cycle; depends on Phases 1-2) - COMPLETE  
[ ] Phase 4: Research Bets & Verification (Adds P vs NP paths; depends on Phase 3)

**Implementation Guidelines** (Unchanged, but emphasize: Start with tiny n; use MLX for any local models if needed.)

---

### Phase 1: Foundation

**Criteria:** Minimal bootstrap for local dev on M4.

[x] **F1. Repository & Tooling Bootstrap**  
[x] Create monorepo with folders: `theory/`, `search/`, `proofs/`, `infra/`, `docs/`.  
[x] Add MIT LICENSE, README.md, CONTRIBUTING.md.  
[x] Makefile with targets: `setup`, `build`, `test`, `verify`, `bench`, `check-proofs`.  
[x] .gitignore for Lean/Python artifacts; pre-commit hooks (ruff, lake fmt).  
[x] Acceptance: `make setup` creates structure, installs deps via Homebrew (Lean 4, Python 3.12, cmake/ninja for solvers).

[x] **F2. Lean 4 Skeleton**  
[x] Init Lean project in `theory/` with lakefile.lean, mathlib dep.  
[x] Minimal lemma/test.  
[x] Acceptance: `make verify` builds/runs test on M4.

[x] **F3. SAT Toolchain**  
[x] Submodule/compile Kissat (ARM64) in `infra/build/`.  
[x] Wrapper in `search/bin/run_kissat` for DRAT/LRAT logs, fixed seeds.  
[x] Acceptance: Solves mini.cnf locally, outputs to `proofs/`.

[x] **F4. Agent Supervisor Skeleton**  
[x] `search/agents/supervisor.py`: Loads YAML plan, sequences agents, logs to JSONL.  
[x] Stub agents: planner, conjecturer (template-based), miner, formalizer, critic.  
[x] Acceptance: `make test` runs dry cycle with stub reports.

---

### Phase 2: Data & Storage

**Criteria:** Basic I/O and artifact handling.

[x] **D1. CNF I/O & Validation**  
[x] `search/io/cnf_reader.py` and `cnf_writer.py` for DIMACS parse/emit.  
[x] Unit tests with fixtures.  
[x] Acceptance: Round-trip preserves semantics.

[x] **D2. Circuit DSL**  
[x] `search/circuits/dsl.py`: Constructors for monotone/AC⁰ circuits.  
[x] `to_cnf.py` for encoding.  
[x] Acceptance: Generates tiny CNF, solves with Kissat.

[x] **D3. Artifact Store**  
[x] SHA256-based store in `proofs/` with index.json metadata.  
[x] `search/tools/inspect_artifacts.py`.  
[x] Acceptance: Registers/logs hashes deterministically.

[x] **D4. Config System**  
[x] `infra/config/defaults.yaml`; load/validate in supervisor.  
[x] Acceptance: Overrides work; invalid fails.

---

### Phase 3: Agents & Core Loop

**Criteria:** End-to-end cycle with interfaces.

[x] **I1. Unified CLI & Reports**  
[x] `satday` CLI (typer): `mine`, `bench`, `check-proofs`, `verify`.  
[x] `search/reporting/md_reporter.py`: Markdown summaries to `docs/reports/`.  
[x] --offline flag to block networks.  
[x] Acceptance: Commands run cycles, produce reports/logs.

[x] **R1. Planner Agent**  
[x] Rule-based decomposition for bets; YAML plans with tasks/seeds.  
[x] Acceptance: Schedules/logs a plan.

[x] **R2. Conjecturer Agent (Template-Based)**  
[x] Grammar-driven generation of Lean stubs/CNF specs.  
[x] Acceptance: Emits stubs/specs to folders.

[x] **R3. Counterexample Miner**  
[x] Synthesize CNF, run Kissat; extract patterns from logs.  
[x] Acceptance: Outputs counterexample or confidence boost.

[x] **R4. Formalizer Agent**  
[x] Tactic library for induction/encodings.  
[x] Convert templates to Lean theorems (with sorry if needed).  
[x] Acceptance: `make verify` compiles.

[x] **R5. Proof Critic (Barrier-Aware)**  
[x] Heuristic tags for relativizing/natural proofs; oracle diagnostics.  
[x] Acceptance: Reports tags/rationale.

[x] **R10. Proof Artifact Round-Trip**  
[x] Reference LRAT logs in Lean (hash-anchored).  
[x] `make check-proofs` replays/verifies.  
[x] Acceptance: Hash breaks fail build.

[x] **R11. Deterministic Bench Harness**  
[x] Seed matrix for small CNFs; CSV/MD summaries.  
[x] Acceptance: Repeatable results.

---

### Phase 4: Research Bets & Verification

**Criteria:** Apply loop to bets; start with one for MVP.

[ ] **R6. Restricted-Circuit Lower Bounds (Bet A)**  
[ ] Prove baseline bounds in Lean; mine patterns from CNF.  
[ ] Acceptance: One proved lower bound with artifact.

[ ] **R7. Algorithm Synthesis (Bet B)**  
[ ] Schema search; prove bounds via induction.  
[ ] Acceptance: One schema with proved polynomial bound.

[ ] **R8. Hardness-vs-Randomness (Bet C)**  
[ ] Correlation tests; formalize implications in Lean.  
[ ] Acceptance: Checked implication for bounded sizes.

[ ] **R9. Barrier-Aware Reductions (Bet D)**  
[ ] Non-relativizing encodings; diagnostics.  
[ ] Acceptance: Documented reduction with partial proof.

**Priority Classification**  
* **Critical:** F1-F4, D1-D3, I1, R1-R5, R10-R11  
* **High:** R6-R9  
* **Status Tracking** (Unchanged)