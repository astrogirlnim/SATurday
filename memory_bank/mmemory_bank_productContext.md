# Product Context: Why SATurday Exists

## The Problem Space

### P vs NP: The Grand Challenge
P vs NP is the most important unsolved problem in computer science, with a $1 million Clay Prize. Traditional approaches have hit fundamental barriers:
- **Relativization Barrier**: Many proof techniques fail because they work identically with or without oracle access
- **Natural Proofs Barrier**: Most lower-bound methods would contradict cryptographic assumptions if scaled up
- **Algebraization Barrier**: Techniques using low-degree polynomials are blocked

### Current Landscape Gaps
1. **Manual Research is Slow**: Complexity theory progress requires years of human effort per small result
2. **No Systematic Exploration**: Most research follows intuition rather than exhaustive search of proof space
3. **Verification Overhead**: Informal proofs can contain subtle errors; formal verification is time-consuming
4. **Barrier Blindness**: Researchers often unknowingly use relativizing techniques that are fundamentally limited
5. **Limited Tooling**: No integrated systems for automated conjecture, counterexample mining, and formal proof

### Existing Competitors and Their Limitations
- **Ax-Prover/Hilbert/Seed Prover**: General theorem proving systems, not complexity-focused; miss barrier awareness
- **LLM-based proof assistants**: Prone to hallucination without formal verification; cloud-dependent and expensive
- **Manual Lean/Coq**: Powerful but requires expert human guidance at every step
- **SAT solver research**: Focuses on solving, not on extracting insights for complexity theory

## SATurday's Unique Value Proposition

### What Makes This Different
1. **Agent-Driven Automation**: Five specialized agents work in concert, handling planning, generation, mining, proof, and critique without constant human intervention
2. **Barrier-Aware by Design**: The Proof Critic explicitly checks for relativization/natural-proof patterns, steering research toward non-blocked paths
3. **Verified Every Step**: Hybrid verification through LRAT-checked SAT proofs AND Lean 4 formal proofs - no hallucinations
4. **Zero-Cost Local**: Runs entirely on consumer hardware (M4 MacBook); no cloud spend after initial setup
5. **Intermediate Value**: Even if P vs NP isn't resolved, the system generates publishable results (new circuit bounds, algorithm proofs, H↔R implications)

### User Experience Goals
- **For Solo Researchers**: Democratizes high-stakes complexity research; enables individual developers to explore paths that previously required large teams
- **For Formal Methods Community**: Provides real-world stress test for Lean theorem proving on open mathematical problems
- **For SAT Practitioners**: Demonstrates SAT solvers as scientific instruments for extracting complexity-theoretic insights, not just solving
- **For Complexity Theorists**: Offers systematic exploration tool that might surface non-obvious proof strategies

## The Research Loop Philosophy

### Why Agent-Based Architecture
Traditional proof assistants are reactive - they wait for human tactics. SATurday inverts this:
1. **Planner**: Autonomously decomposes research bets into testable micro-conjectures
2. **Conjecturer**: Generates variations systematically via templates (or optional local LLM)
3. **Miner**: Uses SAT solvers as scientific instruments - patterns in UNSAT proofs inform general theorems
4. **Formalizer**: Converts insights into machine-checked Lean proofs with tactic libraries
5. **Critic**: Analyzes proofs for barrier violations; suggests non-relativizing modifications

This creates a virtuous cycle: conjecture → test → formalize → critique → refine.

### Bet-Driven Strategy
Rather than attacking P vs NP head-on, SATurday pursues four parallel "bets" that each have intrinsic value:
- **Circuit Lower Bounds**: Even restricted results (monotone, AC⁰) are publishable and build theory
- **Algorithm Synthesis**: Proved time bounds for promise problems advance algorithm design
- **Hardness-Randomness**: Formalizing connections between these areas is novel
- **Barrier-Aware Reductions**: Documenting non-relativizing techniques is meta-research contribution

## Success Scenarios

### Minimum Viable Success
- Generate one new proved lower bound for a restricted circuit class
- Produce reproducible artifacts that pass peer review
- Demonstrate automated conjecture-to-proof pipeline works end-to-end

### Moderate Success
- Multiple publishable results across the four bets
- Community adoption as a research tool
- New insights into barrier-circumventing techniques

### Aspirational Success
- Significant progress toward P vs NP resolution
- Discovery of novel non-relativizing proof strategies
- Paradigm shift in how automated reasoning assists open problems

## Design Principles

### Reproducibility as Foundation
- Every run is deterministic (fixed seeds, pinned versions)
- All artifacts are content-addressed (SHA256 hashes)
- Offline-only ensures no external state contamination

### Verification Without Compromise
- SAT solver outputs verified by LRAT checkers (external validation)
- Lean proofs checked by Lean kernel (cannot be fooled)
- No "trust the LLM" - every claim is mechanically verified

### Cost Control as Feature
- Zero marginal cost enables unlimited experimentation
- Local execution ensures data privacy
- No billing surprises; $100 hard cap prevents runaway spending

### Accessibility
- Runs on consumer hardware (no GPU clusters needed)
- Open source with permissive license
- Documentation targets both theorem-proving novices and complexity experts

