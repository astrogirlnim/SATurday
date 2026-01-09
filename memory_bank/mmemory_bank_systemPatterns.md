# System Patterns: Architecture and Design Decisions

## High-Level Architecture

### Agent Supervisor Pattern
**Core Design**: A central supervisor (`search/agents/supervisor.py`) orchestrates agent execution via YAML plans:
- Loads plan specifying task sequence, seeds, size ranges
- Spawns agents in order: Planner → Conjecturer → Miner → Formalizer → Critic
- Aggregates outputs and writes structured logs (JSONL)
- Enforces offline policy and cost guards

**Agent Interface**: All agents implement `AgentBase` with:
- `plan()` - Decompose work into subtasks
- `act()` - Execute primary logic
- `report()` - Generate human and machine-readable outputs

**Benefits**:
- Clean separation of concerns
- Testable in isolation (stub agents for integration tests)
- Extensible (add new agents without modifying supervisor core)

### Hybrid Verification Architecture
**Two-Layer Verification**:
1. **SAT Solver Layer**: 
   - Kissat generates DRAT/LRAT unsatisfiability proofs
   - External LRAT checker verifies (cannot be fooled by buggy solver)
   - Proofs stored in content-addressed store
2. **Lean 4 Layer**:
   - Formal theorems reference external LRAT proofs by hash
   - Lean kernel verifies proof tactics independently
   - Cross-references ensure SAT and Lean claims align

**Why Hybrid**: SAT solvers find counterexamples/patterns quickly; Lean provides general theorems. Together they cover empirical + deductive reasoning.

### Content-Addressed Artifact Store
**Pattern**: All generated artifacts (CNF files, DRAT logs, solver configs) stored in `proofs/` with SHA256 filenames:
```
proofs/
  abc123.cnf       - Input problem
  abc123.lrat      - Proof log
  def456.lean      - Formal theorem referencing abc123.lrat
  index.json       - Metadata registry
```

**Benefits**:
- Deterministic: Same input always produces same hash
- Tamper-evident: Changing file breaks hash references
- Deduplication: Identical artifacts share storage
- Lean theorems hash-anchor external proofs (breaks build if proof modified)

### Deterministic Execution Model
**Key Decisions**:
- **Fixed Seeds**: All randomness (solver, template generation) uses explicit seeds from plan YAML
- **Pinned Dependencies**: Exact versions via `lean-toolchain`, `pyproject.toml` with locked hashes
- **CPU-Only**: No GPU nondeterminism; fixed CPU affinity for benchmarks
- **Offline Policy**: Network blocked via `--offline` flag; guards check for API keys in env/config

**Enforcement Mechanisms**:
- `infra/policy/zero_cost_guard.py` - Fails build if API keys detected
- `search/bin/run_kissat` wrapper - Enforces fixed seeds and CPU limits
- `make verify` - Replays proofs and checks hashes match

### Research Bet Decomposition
**Strategy Pattern**: Each bet (A-D) has dedicated modules with shared interfaces:
- **Bet A (Circuit Lower Bounds)**: `search/circuits/dsl.py` defines monotone/AC⁰ fragments; `to_cnf.py` encodes to SAT (COMPLETE)
- **Bet B (Algorithm Synthesis)**: Schema generators in `search/synthesis/`; recurrence prover in `theory/Algorithms/` (planned)
- **Bet C (Hardness-Randomness)**: Correlation tests in `search/hardness/`; implications in `theory/HardnessRandomness/` (planned)
- **Bet D (Barrier-Aware)**: Non-relativizing encodings in `search/reductions/`; oracle diagnostics in `search/barriers/` (planned)

**Shared Infrastructure**: All bets use common CNF I/O (COMPLETE), artifact store (in progress), and Lean tactic libraries (planned)

## Agent-Specific Patterns

### Planner Agent (Rule-Based Decomposition)
**Approach**: No LLM; uses hand-coded rules to break bets into tasks:
- Reads bet specification (circuit class, size range, target theorem)
- Generates task matrix: (circuit_type, n, seed) tuples
- Emits YAML plan with dependency DAG
- Tracks milestones and acceptance thresholds

**Design Choice**: Rule-based avoids LLM cost and ensures deterministic planning

### Conjecturer Agent (Template + Optional LLM)
**Two Modes**:
1. **Template Mode (MVP)**: Grammar-driven generation using `lark`:
   - Circuit templates: Parameterized monotone formulas, AC⁰ circuits
   - Lean stubs: Skeleton lemmas with `sorry` placeholders
   - CNF specs: Problem families for miner
2. **Local LLM Mode (Optional)**: Small model via MLX (InternLM-Math-7B):
   - Cached prompts for determinism
   - Offline inference on M4
   - Validation via template parser (reject invalid outputs)

**Output**: Paired artifacts (Lean stub + CNF spec) for each conjecture

### Counterexample Miner (SAT as Scientific Instrument)
**Core Insight**: UNSAT proofs contain structural information about problem hardness
**Pipeline**:
1. Synthesize CNF from conjecture for small n
2. Run Kissat with fixed seed, capture DRAT/LRAT log
3. If SAT: Extract model as counterexample, invalidate conjecture
4. If UNSAT: Analyze proof structure:
   - Clause distribution (resolution tree shape)
   - Unit propagation patterns
   - Variable elimination order
5. Emit patterns to inform Formalizer

**Design Choice**: Focus on small n (≤20 variables) for fast iteration

### Formalizer Agent (Lean Tactic Library)
**Strategy**: Build reusable tactic library in `theory/Tactics/`:
- Induction scaffolds for parameterized statements
- Circuit size monotonicity lemmas
- Encoding correctness (CNF ↔ circuit equivalence)
- Time bound proofs via recurrence unrolling

**Workflow**:
1. Parse template conjecture
2. Instantiate tactic script from library
3. Attempt proof; emit theorem or `sorry` with TODO
4. `make verify` checks compilation

**Design Choice**: Prefer tactic scripts over LLM-generated proofs (more reliable)

### Proof Critic (Barrier Detection)
**Heuristic Analyzer**:
- **Relativization Check**: 
  - Tag proofs using only "local" operations (no oracle queries)
  - Flag if proof structure identical with/without oracle
  - Suggest arithmetization or interactive-proof gadgets
- **Natural Proofs Check**:
  - Detect if lower bound uses "largeness" and "constructivity"
  - Flag if method would break crypto assumptions
  - Suggest restriction to non-uniform circuits
- **Oracle Diagnostics**:
  - Replay argument with synthetic oracles (e.g., PSPACE-complete)
  - Report if proof fails (good - non-relativizing signal)

**Output**: Markdown report with barrier tags and rationale

## Data Flow Patterns

### End-to-End Cycle
```
YAML Plan → Planner (decompose)
  ↓
Conjecturer (generate Lean stub + CNF spec)
  ↓
Miner (SAT solve, extract patterns)
  ↓  ↓
  ↓  (if SAT) → counterexample → invalidate conjecture
  ↓
  (if UNSAT) → LRAT proof + patterns
  ↓
Formalizer (prove in Lean, reference LRAT hash)
  ↓
Critic (check barriers, suggest improvements)
  ↓
Reports (Markdown summaries + JSONL logs)
```

### Artifact Lineage Tracking
Every artifact includes metadata:
- Parent hashes (e.g., Lean theorem references CNF hash)
- Solver version, seed, timestamp
- Agent that produced it
- Acceptance criteria (pass/fail)

## Interface Patterns

### CLI Design (Typer-Based)
Commands mirror research workflow:
- `satday mine` - Run full research cycle
- `satday bench` - Benchmark deterministic harness
- `satday check-proofs` - Replay LRAT verification
- `satday verify` - Build Lean project

**Flags**: `--offline`, `--config`, `--seed` for reproducibility

### Configuration Hierarchy
1. `infra/config/defaults.yaml` - Base settings
2. Environment variables - Override specific keys
3. `--config` flag - Full custom config
4. Validation via Pydantic schemas (fail fast on invalid)

### Reporting Layers
1. **JSONL Logs**: Machine-readable, one event per line, stable schema
2. **Markdown Reports**: Human-readable summaries in `docs/reports/`
3. **Lean Comments**: Inline documentation in formal proofs
4. **Optional TUI**: Real-time progress via `textual` library

## Build and Verification Patterns

### Makefile Targets (Single Entry Point)
- `make setup` - Bootstrap environment (Homebrew, Python venv, Lean)
- `make build` - Compile Lean, build solvers
- `make test` - Run pytest (Python) + lake test (Lean)
- `make verify` - Full verification (Lean build + LRAT replay)
- `make bench` - Deterministic benchmark harness
- `make check-proofs` - Validate artifact hashes

### Pre-commit Hooks
- `ruff` + `black` for Python formatting
- `lake fmt` for Lean formatting
- Enforced via `.pre-commit-config.yaml`

### Zero-Cost Guard Integration
Wired into `make verify`:
```bash
python infra/policy/zero_cost_guard.py || exit 1
```
Fails if:
- API keys in environment
- Outbound network calls in trace
- Non-pinned dependencies

## Scalability Patterns

### Start Small, Prove Principle
- MVP targets n ≤ 10 variables for circuits
- Single conjecture per bet initially
- Expand size/breadth after end-to-end works

### Parallelization Strategy (Future)
- Task matrix naturally parallelizable (independent seeds)
- Current: Sequential for simplicity
- Future: Spawn worker pool for mining phase

### Incremental Formalization
- Conjectures with `sorry` placeholders acceptable initially
- Build tactic library over time
- Tag incomplete proofs with TODOs for human review

## Key Design Tradeoffs

### Template vs LLM Conjecture
- **Decision**: Template-first, LLM optional
- **Rationale**: Determinism, zero cost, faster iteration
- **Tradeoff**: Less creative exploration (mitigated by grammar expressiveness)

### Local vs Cloud
- **Decision**: Fully local on M4
- **Rationale**: Zero marginal cost, privacy, reproducibility
- **Tradeoff**: Slower than GPU clusters (acceptable for MVP scale)

### Small n vs Real-World
- **Decision**: Focus on n ≤ 20 for MVP
- **Rationale**: Fast feedback loops, still theoretically interesting
- **Tradeoff**: Not directly applicable to cryptographic sizes (but principles generalize)

### Hybrid Verification
- **Decision**: Both SAT proofs AND Lean proofs
- **Rationale**: SAT for empirical exploration, Lean for general theorems
- **Tradeoff**: Dual maintenance burden (mitigated by hash-anchoring)

## Implementation Patterns (Phase 2)

### CNF I/O Pattern
**Design**: Separate reader and writer classes with shared data model
**Structure**:
```python
CNFProblem (dataclass)
  - num_vars, num_clauses
  - clauses: List[List[int]]
  - comments: List[str]
  - validate() method

CNFReader
  - read(path) -> CNFProblem
  - read_from_string(content) -> CNFProblem
  - strict mode for validation

CNFWriter
  - write(problem, path)
  - to_string(problem) -> str
  - configurable line width
```

**Benefits**:
- Clean separation: parsing vs writing
- Immutable data model (CNFProblem)
- Validation decoupled from I/O
- Easy testing with string-based I/O

**Usage Pattern**:
```python
reader = CNFReader(strict=True)
problem = reader.read(cnf_path)
if problem.validate()[0]:
    writer = CNFWriter()
    writer.write(problem, output_path)
```

### Circuit DSL Pattern
**Design**: Inheritance hierarchy with constraint validation
**Structure**:
```python
Circuit (base class)
  - Generic gate operations
  - Topology validation
  - Size/depth computation
  
MonotoneCircuit(Circuit)
  - Overrides add_not() to raise error
  - validate() checks no NOT gates
  
AC0Circuit(Circuit)
  - Constructor takes max_depth
  - validate() enforces depth limit
  
FormulaCircuit(Circuit)
  - validate() enforces fan-out 1
```

**Benefits**:
- Type safety: each circuit class enforces its constraints
- Extensible: easy to add new circuit classes
- Testable: each class validates independently
- Clear semantics: circuit type encodes restrictions

**Usage Pattern**:
```python
circuit = MonotoneCircuit(num_inputs=4)
x1, x2 = circuit.add_input(1), circuit.add_input(2)
out = circuit.add_and([x1, x2])
circuit.set_output(out)
assert circuit.validate()  # Checks monotone constraints
```

### Tseitin Encoding Pattern
**Design**: Encoder class with state (variable assignment)
**Algorithm**:
1. Assign CNF variables to gates (inputs map to their indices)
2. Generate clauses for each gate type
3. Add unit clause asserting output is true
4. Return equisatisfiable CNF

**Key Insights**:
- Input gates map to their variable index (x1 → var 1)
- Negated inputs get fresh variables with NOT encoding
- Gate types have fixed clause templates:
  - AND(g, [a,b]): (-g|a), (-g|b), (-a|-b|g)
  - OR(g, [a,b]): (a|b|-g), (g|-a), (g|-b)
  - NOT(g, a): (-g|-a), (g|a)

**Benefits**:
- Linear blowup: O(gates) clauses
- Equisatisfiability preserved
- Deterministic encoding
- Verifiable with SAT solver

**Usage Pattern**:
```python
encoder = CircuitEncoder()
cnf = encoder.encode(circuit)
# CNF is equisatisfiable with circuit
# Solving CNF determines if circuit is SAT
```

### Testing Pattern (Phase 2)
**Structure**:
- Fixtures in `search/tests/fixtures/` (small CNF files)
- Test classes group related tests
- Integration tests verify end-to-end workflows
- pytest fixtures for temp directories

**Test Organization**:
```python
class TestCNFReader:
    # Unit tests for reader
    
class TestCNFWriter:
    # Unit tests for writer
    
class TestRoundTrip:
    # Integration tests for read→write→read
    
class TestKissatIntegration:
    # End-to-end with solver
```

**Benefits**:
- Clear test organization
- Easy to run subsets (pytest -k TestCNFReader)
- Fixtures provide test isolation
- Integration tests catch interaction bugs

