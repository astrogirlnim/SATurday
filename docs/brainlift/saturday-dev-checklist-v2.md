### MVP Checklist

To streamline for a simple MVP, I rewrote it: Reduced to ~25 items by merging redundancies (e.g., combined infra bootstraps, unified CLI/reporting), cut medium/nice-to-haves (F5, I3, I4, R12), made phases more flexible (looser dependencies), and prioritized core agent loop + one bet (A: circuit bounds) for quick wins. Focus: Get a verifiable cycle running locally, producing a tiny proved artifact. Add others iteratively. Retained local-only, testability, and ARM64 notes.

**MVP Development Checklist — SATurday (Zero-Cost, Local-Only Edition)**

**Phases Overview**  
[ ] Phase 1: Foundation (Core setup; independent)  
[ ] Phase 2: Data & Storage (Handles inputs/outputs; depends on Phase 1)  
[ ] Phase 3: Agents & Core Loop (Implements research cycle; depends on Phases 1-2)  
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

[ ] **F3. SAT Toolchain**  
[ ] Submodule/compile Kissat (ARM64) in `infra/build/`.  
[ ] Wrapper in `search/bin/run_kissat` for DRAT/LRAT logs, fixed seeds.  
[ ] Acceptance: Solves mini.cnf locally, outputs to `proofs/`.

[ ] **F4. Agent Supervisor Skeleton**  
[ ] `search/agents/supervisor.py`: Loads YAML plan, sequences agents, logs to JSONL.  
[ ] Stub agents: planner, conjecturer (template-based), miner, formalizer, critic.  
[ ] Acceptance: `make test` runs dry cycle with stub reports.

---

### Phase 2: Data & Storage

**Criteria:** Basic I/O and artifact handling.

[ ] **D1. CNF I/O & Validation**  
[ ] `search/io/cnf_reader.py` and `cnf_writer.py` for DIMACS parse/emit.  
[ ] Unit tests with fixtures.  
[ ] Acceptance: Round-trip preserves semantics.

[ ] **D2. Circuit DSL**  
[ ] `search/circuits/dsl.py`: Constructors for monotone/AC⁰ circuits.  
[ ] `to_cnf.py` for encoding.  
[ ] Acceptance: Generates tiny CNF, solves with Kissat.

[ ] **D3. Artifact Store**  
[ ] SHA256-based store in `proofs/` with index.json metadata.  
[ ] `search/tools/inspect_artifacts.py`.  
[ ] Acceptance: Registers/logs hashes deterministically.

[ ] **D4. Config System**  
[ ] `infra/config/defaults.yaml`; load/validate in supervisor.  
[ ] Acceptance: Overrides work; invalid fails.

---

### Phase 3: Agents & Core Loop

**Criteria:** End-to-end cycle with interfaces.

[ ] **I1. Unified CLI & Reports**  
[ ] `satday` CLI (typer): `mine`, `bench`, `check-proofs`, `verify`.  
[ ] `search/reporting/md_reporter.py`: Markdown summaries to `docs/reports/`.  
[ ] --offline flag to block networks.  
[ ] Acceptance: Commands run cycles, produce reports/logs.

[ ] **R1. Planner Agent**  
[ ] Rule-based decomposition for bets; YAML plans with tasks/seeds.  
[ ] Acceptance: Schedules/logs a plan.

[ ] **R2. Conjecturer Agent (Template-Based)**  
[ ] Grammar-driven generation of Lean stubs/CNF specs.  
[ ] Acceptance: Emits stubs/specs to folders.

[ ] **R3. Counterexample Miner**  
[ ] Synthesize CNF, run Kissat; extract patterns from logs.  
[ ] Acceptance: Outputs counterexample or confidence boost.

[ ] **R4. Formalizer Agent**  
[ ] Tactic library for induction/encodings.  
[ ] Convert templates to Lean theorems (with sorry if needed).  
[ ] Acceptance: `make verify` compiles.

[ ] **R5. Proof Critic (Barrier-Aware)**  
[ ] Heuristic tags for relativizing/natural proofs; oracle diagnostics.  
[ ] Acceptance: Reports tags/rationale.

[ ] **R10. Proof Artifact Round-Trip**  
[ ] Reference LRAT logs in Lean (hash-anchored).  
[ ] `make check-proofs` replays/verifies.  
[ ] Acceptance: Hash breaks fail build.

[ ] **R11. Deterministic Bench Harness**  
[ ] Seed matrix for small CNFs; CSV/MD summaries.  
[ ] Acceptance: Repeatable results.

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