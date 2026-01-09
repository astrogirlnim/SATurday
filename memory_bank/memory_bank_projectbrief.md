# Project Brief: SATurday

## Project Name
**SATurday** - Agent-Driven Research Loop for P vs NP Exploration

## Core Mission
Build a zero-cost, local-only agent-driven research system on MacBook Pro M4 that programmatically explores paths toward resolving P vs NP. The system operates entirely offline, producing verified, publishable artifacts through an autonomous multi-agent cycle.

## Project Goals
1. **Automated Research Loop**: Implement five coordinated agents (Planner, Conjecturer, Counterexample Miner, Formalizer, Proof Critic) that cycle through conjecture generation, refutation/mining, formal proof, and barrier checking
2. **Verified Outputs**: All results are formally verified via DRAT/LRAT proof logs and Lean 4 theorems, ensuring scientific rigor
3. **Zero-Cost Operation**: Hard $100/month kill-switch; runs entirely locally on M4 hardware with no cloud dependencies
4. **Publishable Artifacts**: Generate intermediate results (circuit lower bounds, algorithm proofs, hardness-randomness implications) that are publication-ready
5. **Barrier Awareness**: Explicitly detect and work around known complexity-theoretic barriers (relativization, natural proofs)

## Research Bets (Four Core Paths)
- **Bet A: Restricted-Circuit Lower Bounds** - Prove formal lower bounds for monotone/AC⁰/formula fragments
- **Bet B: Algorithm Synthesis with Proofs** - Learn algorithm schemas and prove polynomial bounds via recurrences/induction
- **Bet C: Hardness-vs-Randomness Workbench** - Formalize micro-implications linking circuit hardness to derandomization
- **Bet D: Barrier-Aware Reductions** - Design non-relativizing encodings with oracle diagnostics

## Success Criteria
- At least one new formally proved lower bound (even if restricted to specific circuit classes)
- At least one algorithm schema with Lean-proved polynomial time bound
- Formalized hardness-randomness implication for bounded circuit sizes
- Documented non-relativizing reduction with partial Lean proof
- All artifacts reproducible with deterministic seeds and hash verification

## Constraints
- **Hardware**: MacBook Pro M4 (ARM64) only
- **Cost**: Zero ongoing costs; no paid APIs or cloud services
- **Network**: Offline-only during execution; no outbound calls
- **Verification**: Every claim must have either LRAT-verified SAT proof or Lean 4 formal proof
- **Reproducibility**: Pinned dependencies, fixed seeds, deterministic builds

## Target Audience
- Complexity theorists and formal methods researchers
- SAT/SMT practitioners and algorithm designers
- Theorem proving communities (Lean/Coq/Isabelle)
- Broader tech audience tracking P vs NP progress

## Repository Structure
```
theory/      - Lean 4: circuits, reductions, complexity scaffolding
search/      - Python: agent supervisor, SAT/SMT, circuit DSL
proofs/      - DRAT/LRAT artifacts, checker configs, hashes
infra/       - Build scripts, config, policy enforcement
docs/        - Reports, papers, barrier notes
```

## Development Philosophy
- Start with tiny n to iterate quickly
- Only promote conjectures with invariant properties to Lean proofs
- Template-based generation before LLMs (cost control)
- Extensive logging at every step
- Test with real runs, not mock data
- Clean folder structure with deep nesting for organization

