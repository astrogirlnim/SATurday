# SATurday: Proof Complexity Ladder for P vs NP

A local research program climbing toward P vs NP through certified proof
complexity lower bounds, rebooted 2026-08-03 after a full program audit.

## Overview

SATurday runs single-cycle research sessions against a ladder of rungs, each a
crisp falsifiable statement about propositional proof systems. The summit link
is a theorem, not a hope: super-polynomial lower bounds for all propositional
proof systems imply NP != coNP (Cook-Reckhow), which implies P != NP.

**Key properties:**
- **Certified or it does not exist**: a result is a Lean 4 certificate that
  compiles with zero sorries and only the three standard axioms (propext,
  Classical.choice, Quot.sound), enforced by `scripts/check_axioms.sh`.
- **Prose first, certify second**: arguments are searched in natural language
  with explicit gap lists, audited for barriers, then formalized. This mirrors
  the pipeline behind the [OpenAI ten-proofs release (2026-08-01)](https://openai.com/index/openai-ten-proofs/).
- **Budgeted empiricism**: SAT solver runs calibrate conjectures under hard cost
  estimates and wall-clock caps; empirical artifacts are hash-addressed and are
  never converted into axioms.
- **Append-only memory**: the ladder (`docs/ladder/ladder.md`) and per-rung
  memory files are the single source of research truth.

## The Ladder

- R0 (certified): resolution soundness and refutational completeness
  (`theory/Theory/ProofComplexity/Resolution.lean`).
- R1 (active): Haken's exponential lower bound for pigeonhole formulas;
  family and non-vacuity witness certified, bound stated in a quarantined
  Frontier namespace (`theory/Theory/ProofComplexity/PHP.lean`).
- R2: width machinery (Ben-Sasson-Wigderson), Tseitin and random k-CNF bounds.
- R3: one certified bound above resolution.
- R4: the open frontier (AC0[p]-Frege and beyond).
- R5: the Cook-Reckhow bridge formalized over a real machine model.

Postmortems for the retired pre-reboot program (vacuous monotone parity target,
sheaf obstruction closure) are in `docs/postmortems/`. Pre-reboot ORACLE
artifacts (brainlift notes, bet configs, oracle logs) are in `archive/pre-reboot/`.

## Architecture

```
theory/    - Lean 4 formal proofs (proof complexity ladder modules)
search/    - Python tooling (budgeted falsifier runner, CNF families, artifact store)
proofs/    - CNF/proof artifacts, content-addressed store (index.json)
infra/     - Build scripts (kissat), configs
docs/      - Ladder state, rung memories, attack docs, postmortems, checklists
scripts/   - Axiom gate (check_axioms.sh, accepted_declarations.txt)
archive/   - Retired pre-reboot program, kept for reference
```

## Sessions and Skills

The canonical entrypoint is the `saturday` cursor skill: one session, one rung,
one action (`prove`, `formalize`, `falsify`, or `audit` via the `prover`,
`formalizer`, `falsifier`, `barrier-auditor` skills), one rung memory append,
one line in `search/logs/saturday_sessions.jsonl`, stop. Three human gates:
adopting or killing a rung, accepting a prose proof for formalization, and
merging a certified result.

## Quick Start

```bash
# Build the Lean library (requires elan; mathlib cache in theory/.lake)
cd theory && lake build

# Run the acceptance gate (build + sorry quarantine + axiom check)
./scripts/check_axioms.sh

# Run a budgeted falsifier baseline (deterministic, hard caps)
python3 search/bin/run_proof_size_baseline.py --family php --n-min 4 --n-max 10 --seed 42
```

## Requirements

- macOS on Apple Silicon (tested on M4), 16GB+ RAM
- Lean 4 toolchain pinned by `theory/lean-toolchain` (v4.30.0-rc1) via elan
- Python 3.11+ (the falsifier runner is stdlib-only)
- kissat 3.1.1 (built at `infra/build/kissat`)

## Standards

- `docs/p-vs-np-proof-standards.md`: acceptance bar and frontier quarantine
- `docs/p-vs-np-stop-conditions.md`: stop rules and resource budgets
- `docs/p-vs-np-main-attack.md`: the locked attack and reopen conditions
- `docs/p-vs-np-barrier-evasion.md`: barrier and limitative-result audit spec

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for development guidelines.

## License

MIT License - see [LICENSE](LICENSE) for details.

## Acknowledgments

Built with:
- [Lean 4](https://lean-lang.org/) - Formal verification
- [Kissat](http://fmv.jku.at/kissat/) - SAT solving
- [mathlib](https://github.com/leanprover-community/mathlib4) - Mathematical foundations

---

**Note**: This is a research project. A result exists here only as a
machine-checkable Lean certificate; everything else is calibration or
work in progress.
