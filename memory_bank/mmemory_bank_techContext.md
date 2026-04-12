# Technical Context: Technologies and Development Setup

**Memory bank review:** 2026-04-12. Core filenames use the `mmemory_bank_*.md` prefix
under `memory_bank/`.

## Hardware Platform
**Target**: MacBook Pro with M4 chip (ARM64 architecture)
- **RAM**: Minimum 16GB, recommended 32GB+ for larger models
- **Storage**: Minimum 50GB free for dependencies and artifacts
- **CPU**: ARM64 native compilation for all tools
- **GPU**: Not used (determinism constraint); CPU-only execution

## Core Technologies

### Formal Verification Stack
**Lean 4** (Primary Theorem Prover)
- Version: v4.27.0-rc1 (pinned via `lean-toolchain` file in `theory/`)
- Dependencies: `mathlib4` from GitHub (auto-cached, 7,811 build artifacts)
- Build: `lake` v5.0.0-src+2fcce72 (Lean's package manager)
- IDE: VSCode with Lean extension (optional, not required for CLI)
- Testing: Type-checking IS the test - if proofs compile, they're valid

**Why Lean 4**:
- Modern type theory with dependent types
- Strong tactic library (mathlib)
- Active community in formal math
- ARM64 support via official builds

**Alternatives Considered**:
- Coq: More mature but heavier
- Isabelle: Less suitable for constructive proofs

### Circuit DSL Components (Phase 2)
**Circuit Types** (all implemented):
- **Generic Circuit**: Base class with AND/OR/NOT/INPUT gates
  - Size and depth computation
  - Topology validation (cycle detection)
- **MonotoneCircuit**: Restricted to AND/OR (no NOT except on inputs)
  - Enforces monotone constraint
- **AC0Circuit**: Constant-depth, unbounded fan-in
  - Configurable depth limit
- **FormulaCircuit**: Fan-out 1 (tree structure)
  - Tree topology validation

**Tseitin Encoding**:
- Circuit-to-CNF transformation
- Equisatisfiable encoding (preserves satisfiability)
- AND gate: 3 clauses
- OR gate: 3 clauses  
- NOT gate: 2 clauses
- Overhead: ~3-4 clauses per gate

**Helper Functions**:
- build_and_tree() - Balanced AND tree
- build_or_tree() - Balanced OR tree

### SAT/SMT Solving Stack
**Kissat** (Primary SAT Solver)
- ARM64 compiled via `infra/build/kissat_build.sh`
- Flags: `--unsat` for DRAT/LRAT proof generation
- Fixed seed support for determinism
- Wrapper: `search/bin/run_kissat` enforces policy

**LRAT Checker** (Proof Verification)
- Options: `lrat-check` (from SAT competition tools)
- Purpose: External validation of Kissat UNSAT claims
- Integration: `make check-proofs` replays all stored proofs

**Why Kissat**:
- Fast on small instances (< 100k clauses)
- Clean LRAT output
- Well-maintained, stable

**Alternatives Considered**:
- CaDiCaL: Similar performance, also good choice
- Z3 SMT: Overkill for pure SAT problems

### Python Stack
**Version**: Python 3.12+ (via Homebrew on macOS, but 3.11.3 via pyenv also works)
**Environment**: `venv` for isolation
**Key Libraries** (Installed):
- `pyyaml` 6.0.3 - YAML parsing for execution plans
- `pytest` 9.0.2 - Testing framework (68 tests passing)
- `typer` 0.21.1 - CLI framework (modern, type-safe) ✓ INSTALLED
- `rich` 14.2.0 - Terminal output formatting (tables, colors) ✓ INSTALLED
- `pydantic` 2.12.5 - Config validation with schemas ✓ INSTALLED
- `pydantic-core` 2.41.5 - Pydantic runtime
- `click` 8.3.1 - CLI toolkit (typer dependency)
- `shellingham` 1.5.4 - Shell detection (typer dependency)
- `markdown-it-py` 4.0.0 - Markdown parsing (rich dependency)
- `pygments` 2.19.2 - Syntax highlighting (rich dependency)
**Planned**:
- `lark` - Grammar parsing for template generation
- `ruff` + `black` - Linting and formatting
- `textual` - Optional TUI interface

**CNF/SAT Libraries**:
- Custom parsers in `search/io/` for DIMACS format (production-ready)
  - cnf_reader.py (289 lines) - Strict DIMACS parser
  - cnf_writer.py (185 lines) - DIMACS writer
- `pysat` - Python SAT toolkit (planned for advanced features)

**Why Python**:
- Excellent for orchestration and scripting
- Strong SAT ecosystem (pysat)
- Fast development iteration
- Good ARM64 support

### Local LLM Stack (Optional, Phase 4)
**Inference Engine**: MLX (Apple Silicon optimized)
- Native ARM64/Metal acceleration
- Unified memory model (CPU+GPU)
- Open source from Apple ML Research

**Model Recommendations**:
- **InternLM-Math-7B**: Math reasoning, Lean integration
- **DeepSeek-Math-7B**: Alternative math model
- **WizardMath-7B**: Good for reasoning chains

**Quantization**: 4-bit or 8-bit via MLX for memory efficiency
**Why MLX**: Fastest inference on M4, zero cost, fully local

**Alternatives**:
- `llama.cpp`: Cross-platform but slower on M4
- `Ollama`: Good UX but extra abstraction layer

### Build and Dependency Management

**Make** (Orchestration)
- Single `Makefile` at repo root
- Targets: `setup`, `build`, `test`, `verify`, `bench`, `check-proofs`
- Portable across macOS versions

**Homebrew** (System Dependencies)
- Lean 4 toolchain
- Python 3.12+
- cmake, ninja (for compiling solvers)
- gcc-llvm (ARM64 compiler)

**Lake** (Lean Package Manager)
- Defined in `theory/lakefile.lean`
- Pinned mathlib version
- Handles Lean dependencies

**pyproject.toml** (Python Dependencies)
- PEP 621 compliant
- Locked with `pip-tools` or `uv` for exact versions
- Includes `--hash` entries for security

### Version Control and Pre-Commit
**Git** with sensible `.gitignore`:
- Python artifacts: `__pycache__`, `.pytest_cache`, `*.pyc`
- Lean artifacts: `build/`, `.lake/`, `lake-packages/`
- Solver builds: `infra/build/kissat`, `*.o`, `*.a`
- IDE configs: `.vscode/`, `.idea/`

**Pre-Commit Hooks**:
```yaml
repos:
  - repo: https://github.com/astral-sh/ruff-pre-commit
    hooks:
      - id: ruff
      - id: ruff-format
  - repo: local
    hooks:
      - id: lean-format
        name: Lean Format
        entry: lake fmt
        language: system
```

### Configuration Management
**YAML** (Human-Readable Config)
- `infra/config/defaults.yaml` - Base configuration
- `infra/config/schemas.py` - Pydantic validation models

**Environment Variables** (Overrides)
- `SATURDAY_OFFLINE=1` - Force offline mode
- `SATURDAY_CONFIG=/path/to/config.yaml` - Custom config
- `SATURDAY_SEED=42` - Global seed override

### Artifact Storage
**Filesystem-Based Store** (`proofs/`)
- SHA256-named files for content addressing
- `index.json` for metadata (timestamp, tool versions, lineage)
- Flat structure (no deep nesting) for simplicity

**Hash Function**: SHA256 via Python `hashlib`
**Indexing**: JSON for easy inspection and tooling

### Logging and Reporting
**JSONL** (Machine Logs)
- One JSON object per line: `{"timestamp": "...", "agent": "...", "event": "...", "data": {...}}`
- Append-only: Easy to tail/parse
- Schema stability: Required fields documented

**Markdown** (Human Reports)
- Template-based via Python string formatting or Jinja2
- Output to `docs/reports/YYYY-MM-DD-HHMMSS.md`
- Includes links to artifacts, stats, acceptance verdicts

**Lean Comments** (Inline Docs)
- Doc comments (`/-! ... -/`) for theorems
- Cross-references to external proofs: `-- LRAT: proofs/abc123.lrat`

### Testing Infrastructure
**pytest** (Python Unit Tests)
- pytest 9.0.2 installed and working
- Fixtures in `search/tests/fixtures/` (5 CNF test files)
- Test suites:
  - test_cnf_io.py (16 tests) - CNF reader/writer
  - test_circuits.py (21 tests) - Circuit DSL and encoding
- Total: 37 tests, all passing (100% pass rate)
- Execution time: 40-60ms for unit tests
- Coverage reporting (optional) - not yet implemented

**lake build** (Lean Tests)
- Tests are theorems in `theory/Theory/Tests/`
- If theorems type-check, tests pass (no separate test framework)
- Use `lake build Theory.Tests.BasicTests` to verify
- Regression suite for tactic library built via theorem compilation

**Acceptance Tests**:
- Documented in checklist items
- Executed via `make test` or `make verify`
- Human-verified initially, automated later

### Offline Policy Enforcement
**Zero-Cost Guard** (`infra/policy/zero_cost_guard.py`)
- Scans environment for API keys: `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, etc.
- Checks git history for accidental commits of secrets
- Validates config files have no cloud endpoints
- Exit code 1 if violations found

**Network Blocking** (OS-Level)
- `--offline` flag in CLI disables DNS resolution
- Subprocess wrapper catches socket attempts
- macOS: Can use `pfctl` firewall rules for paranoia

### Documentation Stack (Optional)
**MkDocs** or **mdBook**
- Static site generation from Markdown
- Offline theme (vendored assets, no CDN)
- API docs via `mkdocstrings` for Python

**Why Optional**: MVP can work with just Markdown files

## Development Workflow

### Initial Setup (One-Time)
```bash
# Clone repo
git clone <repo-url> && cd SATurday

# Bootstrap environment
make setup
# This runs:
#   - infra/scripts/bootstrap_macos.sh (Homebrew installs)
#   - Python venv creation with dependencies
#   - Lean project initialization
#   - SAT solver compilation
#   - Pre-commit hook installation
```

### Daily Development Loop
```bash
# Activate Python environment
source venv/bin/activate  # or via uv/pipx

# Edit code...

# Run tests
make test  # pytest + lake test

# Format code (auto via pre-commit)
git commit -m "Implement planner agent"

# Full verification
make verify  # Lean build + LRAT checks
```

### Running Research Cycles
```bash
# Mine conjectures for Bet A (circuit lower bounds)
satday mine --bet=A --n=10 --seed=42 --offline

# Check generated proofs
make check-proofs

# Benchmark deterministic harness
satday bench --config=infra/config/small_bench.yaml
```

## Constraints and Tradeoffs

### ARM64 Compatibility
- **Challenge**: Some SAT tools default to x86 optimizations
- **Solution**: Explicit ARM64 flags in build scripts; test on M4 from day one
- **Tradeoff**: Slightly slower than x86 SIMD, but acceptable for small instances

### Memory Limits (M4 with 16-32GB)
- **Challenge**: Large LLMs (>13B parameters) may not fit
- **Solution**: 4-bit quantization via MLX; use 7B models; prefer templates
- **Tradeoff**: Less creative conjecture generation (mitigated by grammar richness)

### Determinism Requirements
- **Challenge**: GPU execution is often nondeterministic
- **Solution**: CPU-only mode; fixed seeds; pinned deps
- **Tradeoff**: Slower inference (acceptable for offline, overnight runs)

### Offline Operation
- **Challenge**: Cannot download dependencies during run
- **Solution**: Pre-cache all models, pin all package versions, vendor solver binaries
- **Tradeoff**: Larger repo size, more complex setup

## Security Considerations

### Secrets Management
- **Never**: Commit API keys, tokens, or credentials
- **Enforcement**: `zero_cost_guard.py` fails builds with secrets
- **Storage**: Use environment variables only; add to `.gitignore`

### Supply Chain
- **Dependencies**: Hash-pinned in `pyproject.toml`
- **Solvers**: Compile from source with submodules (auditable)
- **Models**: Download once, hash-check, vendor locally

### Sandboxing (Future)
- Consider running agents in separate processes with restricted syscalls
- For MVP: Offline policy is sufficient isolation

## Performance Targets (MVP)

### Solver Performance
- Small instances (n=10): < 1 second
- Medium instances (n=20): < 10 seconds
- Goal: Fast iteration, not competition-level speed

### Lean Compilation
- Minimal project: < 30 seconds on M4
- With mathlib: < 5 minutes (cached)
- Incremental builds: < 10 seconds for single file

### End-to-End Cycle
- One complete conjecture-to-proof cycle: < 1 minute for tiny n
- Full benchmark harness (10 conjectures): < 10 minutes
- Nightly research run: < 1 hour (future scaling)

## Monitoring and Observability

### Logs
- `search/logs/` - JSONL per run
- Structured fields: timestamp, agent, event, data
- Retention: Keep all (disk is cheap)

### Metrics (Informal)
- Count of conjectures generated
- SAT vs UNSAT ratio
- Lean proof success rate
- Barrier detection frequency

**No Telemetry**: Everything is local; no external reporting

## Upgrade Strategy

### Dependencies
- Monthly: Check for Lean/mathlib updates
- Quarterly: Update Python packages
- Procedure: Update lock file, run full test suite, commit

### Backward Compatibility
- Artifact store format: Versioned metadata
- YAML plans: Schema evolution with migrations
- Lean theorems: Semantic versioning for tactic library

## Debugging Tools

### Python Debugging
- `pytest --pdb` for interactive debugging
- `rich.print()` for structured console output
- JSONL logs for post-mortem analysis

### Lean Debugging
- `#check` and `#eval` for interactive proofs
- VSCode extension for inline error messages
- `lake build --verbose` for detailed build logs

### SAT Debugging
- `search/tools/inspect_artifacts.py` to decode LRAT proofs
- DIMACS validation with `cnf_reader.py`
- Manual solver invocation with `run_kissat` wrapper

## Known Limitations (MVP Scope)

### Scale
- MVP targets n ≤ 20 (not cryptographic sizes)
- Single-machine only (no distributed execution)

### Automation
- Template-based generation may miss creative conjectures
- Human review still needed for barrier analysis

### Formalization Coverage
- Not all conjectures will have Lean proofs initially
- `sorry` placeholders acceptable for incremental progress

### Cost
- $0 marginal cost, but significant setup time investment
- M4 hardware requirement (not free)

## Future Technology Considerations

### Post-MVP Enhancements
- **GPU Acceleration**: MLX for faster LLM inference
- **Parallel Execution**: Multi-core mining phase
- **Larger Models**: 13B-70B with quantization
- **Cloud Backup**: Optional artifact sync (with cost guard)

### Emerging Tools to Watch
- Lean 5 (when released)
- Newer SAT solvers with better ARM64 support
- Improved LLM-to-Lean translation tools (e.g., COPRA successors)

