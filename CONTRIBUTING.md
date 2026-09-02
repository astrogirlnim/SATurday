# Contributing to SATurday

Thank you for your interest in contributing to SATurday! This document provides guidelines for development.

## Development Philosophy

- **Correctness over speed**: All outputs must be formally verified
- **Deterministic by default**: Fixed seeds, pinned dependencies, reproducible builds
- **Offline-first**: No network calls during execution; zero marginal cost
- **Extensive logging**: Every step must be observable and debuggable
- **No placeholders**: Real functionality and data only; no mock implementations

## Getting Started

### Prerequisites

- macOS 14.0+ with Apple Silicon (M4 recommended)
- Homebrew package manager
- 16GB+ RAM
- 50GB+ free storage

### Initial Setup

```bash
# Clone the repository
git clone https://github.com/astrogirlnim/SATurday.git
cd SATurday

# Bootstrap environment
make setup

# Verify installation
make test
make verify
```

## Development Workflow

### Branch Strategy

- `main` - Stable, verified code only
- `develop` - Integration branch for features
- `feature/*` - Individual feature branches
- `fix/*` - Bug fix branches

### Commit Guidelines

Format: `<type>: <description>`

Types:
- `feat` - New feature
- `fix` - Bug fix
- `docs` - Documentation only
- `test` - Test additions or fixes
- `refactor` - Code restructuring
- `perf` - Performance improvements
- `chore` - Maintenance tasks

**Important**: Never use backslashes or forward slashes in commit messages (breaks formatting).

Example:
```bash
git commit -m "feat: implement planner agent decomposition logic"
git commit -m "fix: correct LRAT hash verification in artifact store"
```

### Code Style

**Python**:
- Use `ruff` for linting and `black` for formatting (automated via pre-commit)
- Type hints required for all function signatures
- Docstrings for all public functions (Google style)
- Maximum line length: 100 characters

**Lean**:
- Use `lake fmt` for formatting (automated via pre-commit)
- Doc comments (`/-! ... -/`) for all public theorems
- Prefer tactic mode over term mode for readability

### Testing Requirements

All contributions must include tests:

1. **Unit Tests**: Test individual functions/modules
   ```bash
   pytest search/tests/test_cnf_reader.py -v
   ```

2. **Integration Tests**: Test agent interactions
   ```bash
   pytest search/tests/integration/ -v
   ```

3. **Lean Tests**: Verify formal proofs compile
   ```bash
   cd theory && lake test
   ```

4. **Acceptance Tests**: Verify checklist criteria
   - Document acceptance criteria in PR description
   - Manual verification initially; automate high-value tests

### Logging Standards

**Every operation must log**:

```python
# Python logging
import logging
logger = logging.getLogger(__name__)

# Log all decisions and state changes
logger.info(f"Starting CNF synthesis for n={n}, seed={seed}")
logger.debug(f"Generated {len(clauses)} clauses")
logger.info(f"CNF synthesis complete: {output_path}")
```

```lean
-- Lean comments
-- LOG: Starting proof of lower bound for monotone circuits
-- LOG: Applying induction on circuit depth
-- LOG: Proof complete, artifact hash: abc123...
```

### Pre-Commit Hooks

Hooks run automatically on `git commit`:
- `ruff` - Python linting
- `black` - Python formatting
- `lake fmt` - Lean formatting

To run manually:
```bash
pre-commit run --all-files
```

## Project Structure

```
SATurday/
├── theory/          # Lean 4 formal proofs
│   ├── Theory/      # Main theory modules
│   ├── Tactics/     # Reusable proof tactics
│   └── Tests/       # Lean test cases
├── search/          # Python agent system
│   ├── agents/      # Agent implementations
│   ├── circuits/    # Circuit DSL
│   ├── io/          # CNF/DIMACS I/O
│   ├── storage/     # Artifact store
│   └── tests/       # Python tests
├── proofs/          # LRAT artifacts (content-addressed)
├── infra/           # Build and config
│   ├── build/       # Solver compilation
│   ├── config/      # YAML configs
│   └── scripts/     # Setup scripts
└── docs/            # Documentation
    ├── ladder/      # Ladder state and rung memories
    ├── postmortems/ # Retired program postmortems
    └── reports/     # Generated run reports (gitignored)
```

Pre-reboot ORACLE program artifacts live under `archive/pre-reboot/`.

## Adding New Features

### 1. Agent Development

New agents must implement `AgentBase`:

```python
from search.agents.core import AgentBase

class MyAgent(AgentBase):
    def plan(self, config: dict) -> list[Task]:
        """Decompose work into subtasks."""
        # LOG: Planning phase started
        pass
    
    def act(self, task: Task) -> Result:
        """Execute agent logic."""
        # LOG: Executing task {task.id}
        pass
    
    def report(self, results: list[Result]) -> Report:
        """Generate human and machine-readable output."""
        # LOG: Generating report for {len(results)} results
        pass
```

### 2. Lean Theorem Development

Theorems must reference external proofs by hash:

```lean
-- LRAT: proofs/abc123def456.lrat
theorem my_lower_bound (n : ℕ) : 
  circuit_size monotone_class n ≥ 2^n := by
  -- LOG: Starting proof for n={n}
  induction n with
  | zero => sorry  -- TODO: Base case
  | succ n ih => sorry  -- TODO: Inductive step
```

### 3. Circuit DSL Extensions

Add new circuit classes to `search/circuits/dsl.py`:

```python
class MyCircuitClass(CircuitClass):
    """Description of circuit restrictions."""
    
    def validate(self, circuit: Circuit) -> bool:
        """Check circuit satisfies class constraints."""
        # LOG: Validating circuit with {circuit.size} gates
        pass
    
    def to_cnf(self, n: int) -> CNF:
        """Encode as CNF for small n."""
        # LOG: Encoding circuit class for n={n}
        pass
```

## Pull Request Process

1. **Create Feature Branch**
   ```bash
   git checkout -b feature/my-feature
   ```

2. **Implement with Tests**
   - Write tests first (TDD encouraged)
   - Implement functionality
   - Add extensive logging
   - Update documentation

3. **Verify Locally**
   ```bash
   make test        # Run all tests
   make verify      # Build Lean and check proofs
   make check-proofs  # Verify LRAT artifacts
   ```

4. **Commit Changes**
   ```bash
   git add .
   git commit -m "feat: implement my feature"
   ```

5. **Push and Create PR**
   ```bash
   git push origin feature/my-feature
   ```

6. **PR Checklist**
   - [ ] Tests pass locally
   - [ ] Code formatted (pre-commit hooks passed)
   - [ ] Documentation updated
   - [ ] Acceptance criteria documented
   - [ ] No API keys or secrets in code
   - [ ] Offline policy maintained (no network calls)

## Debugging Tips

### Python Debugging
```bash
# Interactive debugging
pytest --pdb search/tests/test_miner.py

# Verbose logging
SATURDAY_LOG_LEVEL=DEBUG satday mine --bet=A
```

### Lean Debugging
```bash
# Verbose build
cd theory && lake build --verbose

# Check specific file
lake env lean --run Theory/Circuits.lean
```

### SAT Solver Debugging
```bash
# Manual solver invocation
search/bin/run_kissat examples/test.cnf --verbose

# Inspect LRAT proof
python search/tools/inspect_artifacts.py proofs/abc123.lrat
```

## Code Review Guidelines

Reviewers should check:
- Deterministic execution (fixed seeds, no randomness)
- Extensive logging at all steps
- Tests cover edge cases
- No network calls (offline-first)
- No API keys or secrets
- Documentation updated
- Lean proofs compile
- LRAT proofs verify

## Security

### Secrets Management
- **Never commit** API keys, tokens, or credentials
- Use environment variables only
- Add sensitive patterns to `.gitignore`

### Dependency Verification
- All dependencies must be hash-pinned in `pyproject.toml`
- Lean dependencies pinned via `lakefile.lean`
- Solver binaries compiled from auditable source

## Performance Expectations

Target benchmarks for MVP:
- Kissat solve (n=10): < 1 second
- Lean incremental build: < 10 seconds
- End-to-end cycle: < 1 minute for tiny n
- Full benchmark harness: < 10 minutes

## Community

### Getting Help
- Check existing documentation in `docs/`
- Review related issues and PRs
- Ask questions in discussions (when public)

### Code of Conduct
- Be respectful and constructive
- Focus on ideas, not individuals
- Assume good faith
- Welcome newcomers

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

---

Thank you for helping advance automated complexity theory research!

