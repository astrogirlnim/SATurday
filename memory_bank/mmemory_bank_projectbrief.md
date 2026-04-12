# Project Brief: SATurday

## Core Mission

Automated, zero-cost research system that explores complexity theory (P vs NP) through formal verification, running entirely locally on Apple Silicon (M4 MacBook Pro).

## What We're Building

**Primary pipeline (five agents):**
1. **Planner** - Task decomposition and scheduling
2. **Conjecturer** - Generate Lean stubs and CNF specifications
3. **Miner** - SAT solver integration with LRAT proof extraction
4. **Formalizer** - Lean theorem generation with proof scaffolding
5. **Critic** - Barrier-aware analysis

**ORACLE research loop (Phase 6, optional layered loop):** Nine coordinated roles
(Planner, Algebraist, Geometer, Skeptic, Miner, Reflector, Formalizer, Critic, Guardrail)
documented in `.cursor/skills/run-oracle/SKILL.md` and `mmemory_bank_activeContext.md`.
They sit on top of the same encoders, Kissat, LRAT store, and Lean project.

**Research Bets:**
- **Bet A**: Restricted-Circuit Lower Bounds (monotone, AC0, formula)
- **Bet B**: Algorithm Synthesis with Proved Polynomial Bounds
- **Bet C**: Hardness-vs-Randomness Formalized Implications
- **Bet D**: Barrier-Aware Reductions (non-relativizing techniques)

## Core Requirements

**Zero-Cost Constraint:**
- No cloud APIs or external services
- All computation local (M4 MacBook Pro)
- Deterministic, reproducible execution
- No network dependencies during execution

**Formal Verification:**
- Hybrid LRAT (SAT solver proofs) + Lean 4 (theorem proving)
- Content-addressed artifact store (SHA256 hashing)
- Hash-anchored proof references for tamper-evidence
- Type-checked formal verification of computational results

**Automation:**
- Minimal human intervention
- Agent-driven exploration and verification
- Systematic instance generation and testing
- Automated barrier detection

## Success Criteria

**Immediate (MVP - COMPLETE):**
- 5-agent loop operational
- Circuit synthesis encoding working
- SAT solver integration with LRAT proofs
- Lean theorem generation compiling

**Phase 5 (Current Focus - V1 & V2 COMPLETE):**
- LRAT-Lean integration working (DONE)
- First 3 fully verified theorems (DONE)
- Systematic coverage of Bet A instances
- Publication-ready results

**Long-term:**
- New proved lower bounds (even restricted)
- New non-relativizing reductions
- Tightened hardness-randomness implications
- Publishable stepping stones toward P≠NP

## Non-Goals

- Solving P vs NP directly (long-shot, not expected)
- Cloud-based computation (zero-cost constraint)
- GUI or web interface (CLI-driven)
- Real-time performance (offline batch processing)
