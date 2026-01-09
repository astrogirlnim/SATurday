# SATurday: Agent-Driven Research Loop for P vs NP

An automated, zero-cost research system that explores complexity theory through formal verification.

## Overview

SATurday is a multi-agent system running locally on Apple Silicon (M4) that programmatically investigates paths toward resolving P vs NP. Five specialized agents—Planner, Conjecturer, Counterexample Miner, Formalizer, and Proof Critic—work in concert to generate, test, and formally verify complexity-theoretic conjectures.

**Key Features:**
- **Fully Automated**: Agent-driven research loop requires minimal human intervention
- **Formally Verified**: Hybrid verification via LRAT-checked SAT proofs and Lean 4 theorems
- **Zero Cost**: Runs entirely locally with no cloud dependencies or API fees
- **Offline-First**: Deterministic, reproducible execution with no network calls
- **Barrier-Aware**: Explicitly detects and works around relativization and natural proofs barriers

## Research Bets

SATurday pursues four parallel research directions:

- **Bet A**: Restricted-Circuit Lower Bounds (monotone, AC⁰, formula fragments)
- **Bet B**: Algorithm Synthesis with Proved Polynomial Bounds
- **Bet C**: Hardness-vs-Randomness Formalized Implications
- **Bet D**: Barrier-Aware Reductions (non-relativizing techniques)

## Architecture

```
theory/    - Lean 4 formal proofs (circuits, reductions, complexity scaffolding)
search/    - Python agents (supervisor, SAT/SMT, circuit DSL)
proofs/    - DRAT/LRAT artifacts, checker configs, content-addressed store
infra/     - Build scripts, configs, policy enforcement
docs/      - Reports, papers, development notes
```

## Requirements

- **Hardware**: MacBook Pro with M4 chip (ARM64)
- **RAM**: 16GB minimum, 32GB+ recommended
- **OS**: macOS 14.0+
- **Storage**: 50GB free space

## Quick Start

```bash
# Bootstrap environment (one-time setup)
make setup

# Run a research cycle for circuit lower bounds
satday mine --bet=A --n=10 --seed=42 --offline

# Verify all proofs
make verify

# Check LRAT proof artifacts
make check-proofs

# Run benchmark harness
satday bench
```

## Development Status

**Phase 1: Foundation** (In Progress)
- [x] Repository structure and tooling bootstrap
- [ ] Lean 4 skeleton project
- [ ] SAT toolchain (Kissat with ARM64)
- [ ] Agent supervisor skeleton

See `docs/brainlift/saturday-dev-checklist-v2.md` for full roadmap.

## Technology Stack

- **Lean 4**: Formal theorem proving with mathlib
- **Kissat**: SAT solver with LRAT proof generation
- **Python 3.12+**: Agent orchestration and tooling
- **MLX**: Optional local LLM inference (Apple Silicon optimized)

## Documentation

- [Development Checklist](docs/brainlift/saturday-dev-checklist-v2.md) - MVP implementation plan
- [Project Concept](docs/brainlift/project-concept.md) - Original vision and goals
- [Market Analysis](docs/brainlift/market-analysis.md) - Competitive landscape

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for development guidelines.

## License

MIT License - see [LICENSE](LICENSE) for details.

## Citation

If you use SATurday in your research, please cite:

```
@software{saturday2026,
  title = {SATurday: Agent-Driven Research Loop for P vs NP},
  author = {SATurday Project Contributors},
  year = {2026},
  url = {https://github.com/yourusername/SATurday}
}
```

## Acknowledgments

Built with:
- [Lean 4](https://lean-lang.org/) - Formal verification
- [Kissat](http://fmv.jku.at/kissat/) - SAT solving
- [mathlib](https://github.com/leanprover-community/mathlib4) - Mathematical foundations

---

**Note**: This is a research project exploring automated theorem proving for complexity theory. Results should be verified independently before publication.

