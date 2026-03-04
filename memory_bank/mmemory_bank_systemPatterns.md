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

### Planner Agent (Rule-Based Decomposition) - ✓ IMPLEMENTED
**Approach**: No LLM; uses hand-coded rules to break bets into tasks:
- Reads bet specification (circuit class, size range, target theorem)
- Generates task matrix: (circuit_type, n, seed) tuples
- Emits YAML plan with dependency DAG to search/plans/generated/
- Tracks milestones and acceptance thresholds

**Implementation Details**:
- **Task Dataclass**: Structured representation with fields:
  - task_id (unique identifier)
  - bet (A/B/C/D)
  - circuit_type (monotone/AC0/formula)
  - n (input size)
  - seed (for determinism)
  - target_function (parity/majority/etc)
  - constraints (dict)
- **BetDecomposer**: Strategy pattern for bet-specific decomposition
  - _decompose_circuit_bounds (Bet A): Monotone, AC0, formula circuits with parity/majority
  - _decompose_algorithm_synthesis (Bet B): Placeholder for algorithm schemas
  - _decompose_hardness_randomness (Bet C): Placeholder for H↔R implications
  - _decompose_barrier_aware (Bet D): Placeholder for barrier diagnostics
- **PlanValidator**: Validates consistency
  - Checks milestone thresholds (90% success, 50% warning)
  - Ensures task IDs are unique
  - Validates task structure
- **Milestone Tracking**: Acceptance criteria with thresholds
  - success_threshold: 0.9 (90% tasks must succeed)
  - warning_threshold: 0.5 (50% triggers warning)
  - Tracks completeness, theorem_count, avg_proof_time

**File Structure**:
```python
class Task:
    task_id: str
    bet: str
    circuit_type: str
    n: int
    seed: int
    # ... other fields

class BetDecomposer:
    def decompose(bet, config, seed) -> Tuple[List[Task], List[Milestone]]
    def _decompose_circuit_bounds(...)
    # ... bet-specific methods

class PlanValidator:
    def validate(plan) -> Tuple[bool, List[str]]
```

**Design Choice**: Rule-based avoids LLM cost, ensures deterministic planning, and provides clear bet-specific strategies

### Conjecturer Agent (Template-Based) - ✓ IMPLEMENTED
**Template Mode (MVP)**: Template-based generation (no grammar parser yet):
- Circuit templates: Parameterized monotone, AC⁰, formula circuits
- Lean stubs: Skeleton theorems with `sorry` placeholders
- CNF specs: YAML specifications for miner

**Implementation Details**:
- **ConjectureTemplate (Abstract Base Class)**:
  - `generate_lean_stub(task)`: Produces Lean theorem with imports, namespace, theorem statement
  - `generate_cnf_spec(task)`: Produces YAML with circuit_class, params, target_function, solver_config
  - `instantiate(task)`: Creates Conjecture dataclass with both stub and spec
- **Concrete Templates for Bet A (Circuit Lower Bounds)**:
  - MonotoneParityTemplate: Monotone circuits computing parity
  - MonotoneMajorityTemplate: Monotone circuits computing majority
  - AC0ParityTemplate: Constant-depth circuits computing parity
  - AC0MajorityTemplate: Constant-depth circuits computing majority
  - FormulaParityTemplate: Formula circuits (fan-out 1) computing parity
- **TemplateRegistry**: Centralized lookup
  - `register_template(bet, circuit_type, template)`
  - `get_template(bet, circuit_type) -> ConjectureTemplate`
  - Pre-registered templates for quick lookup
- **Conjecture Dataclass**: Paired output
  - conjecture_id (unique identifier)
  - lean_stub (theorem text)
  - cnf_spec (YAML dict)
  - task_id (parent task)
  - metadata (additional info)
  - `write_lean_stub(output_dir)`: Writes to theory/Conjectures/BetA/
  - `write_cnf_spec(output_dir)`: Writes to search/specs/

**File Structure**:
```python
# search/templates/base.py
class ConjectureTemplate(ABC):
    @abstractmethod
    def generate_lean_stub(task) -> str
    @abstractmethod
    def generate_cnf_spec(task) -> Dict
    def instantiate(task) -> Conjecture

@dataclass
class Conjecture:
    conjecture_id: str
    lean_stub: str
    cnf_spec: Dict
    # ... methods

# search/templates/bet_a_circuits.py
class MonotoneParityTemplate(ConjectureTemplate):
    def generate_lean_stub(task):
        # Returns Lean theorem with monotone parity lower bound
    def generate_cnf_spec(task):
        # Returns YAML spec for monotone parity circuit
```

**Generated Files**:
- Lean stubs: `theory/Conjectures/BetA/{circuit}_{function}_n{n}_s{seed}.lean`
- CNF specs: `search/specs/{circuit}_{function}_n{n}_s{seed}.yaml`

**Output**: Paired artifacts (Lean stub + CNF spec) for each conjecture

**Future Enhancement**: Local LLM mode via MLX (InternLM-Math-7B) for creative exploration beyond templates

### Counterexample Miner (SAT as Scientific Instrument) - ✓ ENHANCED
**Core Insight**: UNSAT proofs contain structural information about problem hardness
**Pipeline**:
1. **Circuit Synthesis Encoding** (NEW): Generate CNF asking "does circuit exist?"
   - Variables for gate types, input selections, gate values per truth table row
   - Constraints for structure, circuit class, functionality
   - UNSAT = proven lower bound (no circuit of given size/type exists)
   - SAT = constructive counterexample (circuit witness)
2. Run Kissat with fixed seed, capture compressed LRAT log
3. If SAT: Extract model as circuit witness, invalidate lower bound
4. If UNSAT: Proven lower bound
   - Extract LRAT proof for verification
   - Analyze proof patterns (size, complexity)
5. Emit patterns to inform Formalizer

**Circuit Synthesis Encoding Pattern** (NEW):
```python
class CircuitSynthesisEncoder:
    """
    Encodes: ∃ circuit C of type T, size ≤ k : C computes f
    
    Variables:
    - Gate types: is_AND[g], is_OR[g] for each gate g
    - Input selection: input_select[g, pos, src] for gate g, input pos, source src
    - Gate values: gate_value[g, row] for gate g, truth table row
    - Auxiliary: left_val[g, row], right_val[g, row] (optimization)
    
    Constraints:
    - Structure: Each gate has exactly one type, two inputs from earlier gates
    - Circuit class: Monotone (AND/OR only), AC0 (depth limit), etc.
    - Functionality: For each truth table row, gates compute correctly
    - Output: Final gate matches target function on all rows
    
    Complexity: O(k² × 2^n) clauses with auxiliary variables
    """


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

### Proof Critic (Barrier Detection) - ✓ IMPLEMENTED
**Approach**: Heuristic static analysis with text-based Lean parsing

**Implementation Details**:
- **ProofParser**: Text-based extraction of Lean proof structure
  - Regex patterns for theorem names, tactics, lemmas, imports
  - Circuit property identification (monotone, parity, size, depth, etc.)
  - Graceful handling of missing files
- **BarrierDetector**: Three heuristic checks with confidence scoring
  - **Relativization Check** (confidence 0.0-1.0):
    - Detects oracle/blackbox operations (non-relativizing signal)
    - Identifies diagonalization without oracle queries (relativizing)
    - Checks for local vs non-local circuit properties
    - Detects arithmetization and interactive proof techniques
    - Returns evidence list and suggestions
  - **Natural Proofs Check** (largeness + constructivity scores):
    - Largeness: Universal quantification, broad circuit classes
    - Constructivity: Explicit construction, counting arguments, efficient computation
    - Flags potential conflicts with crypto assumptions
    - Suggests restrictions to non-uniform circuits
  - **Oracle Diagnostics**: Conceptual oracle testing
    - Identifies core proof technique (induction, case analysis, exponential bounds, etc.)
    - Determines oracle dependence
    - Interprets non-relativizing signals
- **CriticAgent**: Full agent lifecycle with detailed reporting
  - Parses Lean theorems from Formalizer output
  - Applies all three checks with evidence collection
  - Generates barrier tags: RELATIVIZING, NON_RELATIVIZING, NATURAL_PROOF, ORACLE_INDEPENDENT
  - Overall assessment: EXCELLENT, GOOD, MODERATE, CAUTION
  - Produces Markdown reports with recommendations

**File Structure**:
```python
class ProofParser:
    def parse_lean_file(filepath) -> Dict[str, Any]
    def _extract_theorem_name(content) -> str
    def _extract_tactics(content) -> List[str]
    def _extract_circuit_properties(content) -> List[str]

class BarrierDetector:
    def check_relativization(proof_data) -> Dict[str, Any]
    def check_natural_proofs(proof_data, circuit_type) -> Dict[str, Any]
    def oracle_diagnostics(proof_data) -> Dict[str, Any]

class CriticAgent(AgentBase):
    def plan(context) -> Dict[str, Any]
    def act(context, plan) -> AgentResult
    def report(context, result) -> str
```

**Design Choice**: Text-based parsing over AST analysis for MVP simplicity; heuristic checks over formal verification; confidence scores acknowledge uncertainty in barrier detection

**Output**: Markdown report with barrier tags, confidence scores, evidence, and actionable suggestions

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

### CLI Design (Typer-Based) - ✓ IMPLEMENTED (Phase 3 I1)
Commands mirror research workflow:
- `satday mine` - Run full research cycle with agent pipeline
  - Flags: `--bet`, `--n`, `--seed`, `--config`, `--plan`, `--offline`, `--report`
  - Executes supervisor pipeline, generates JSONL logs and Markdown reports
- `satday bench` - Benchmark deterministic harness (placeholder for R11)
  - Flags: `--config`, `--seed-start`, `--seed-count`, `--output`
- `satday check-proofs` - Replay LRAT verification
  - Flags: `--all`, `--hash`, `--verbose`
  - Verifies artifact store integrity, checks LRAT proofs
- `satday verify` - Build Lean project
  - Runs `lake build` in theory/ directory
- `satday info` - Show system information
  - Displays config, enabled agents, artifact store stats, Lean version

**Implementation**: `search/cli.py` (348 lines) with Rich formatting

### Configuration Hierarchy
1. `infra/config/defaults.yaml` - Base settings
2. Environment variables - Override specific keys
3. `--config` flag - Full custom config
4. Validation via Pydantic schemas (fail fast on invalid)

### Reporting Layers - ✓ IMPLEMENTED (Phase 3 I1)
1. **JSONL Logs**: Machine-readable, one event per line, stable schema
   - Generated by supervisor to `search/logs/`
   - Contains: pipeline_start, agent_complete, pipeline_complete events
2. **Markdown Reports**: Human-readable summaries in `docs/reports/` ✓ IMPLEMENTED
   - Generated by `search/reporting/md_reporter.py` (335 lines)
   - Structure: Executive summary, agent results table, configuration, artifacts, next steps
   - Filename format: `YYYY-MM-DD_HH-MM-SS_runid.md`
   - Batch summary support for multiple runs
3. **Rich Terminal Output**: Colored tables and formatting ✓ IMPLEMENTED
   - Via `rich` library for CLI commands
   - Tables for agent results, colored status icons
4. **Lean Comments**: Inline documentation in formal proofs (planned)
5. **Optional TUI**: Real-time progress via `textual` library (planned)

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

