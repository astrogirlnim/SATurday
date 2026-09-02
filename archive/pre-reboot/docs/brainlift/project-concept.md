# Project Name
SATurday

## Project Description
SATurday becomes an **agent-driven research loop** on a MacBook Pro (M4) that programmatically explores paths toward resolving P vs NP. Five small agents—Planner, Conjecturer (LLM-assisted), Counterexample Miner (PySAT/SMT), Formalizer (Lean 4), and Proof Critic (barrier-aware)—cycle over conjecture → refutation/mining → formal proof → barrier check. The system targets four “bets”: (A) automated lower bounds for increasingly strong circuit classes, (B) algorithm-schema synthesis with **proved** polynomial bounds on promised instances, (C) hardness-vs-randomness micro-implications formalized in Lean, and (D) barrier-aware reductions that nudge arguments beyond relativization/natural-proofs. Everything is reproducible (containers, pinned deps), cheap (hard **$100/mo** kill-switch), and verified (DRAT/LRAT + certified checkers, Lean proofs), producing publishable artifacts en route—even while chasing the long-shot prize.

## Target Audience
- [ ] Complexity theorists and formal-methods researchers
- [ ] SAT/SMT practitioners and algorithm designers
- [ ] Theorem-proving communities (Lean/Coq/Isabelle)
- [ ] Broader tech audience tracking P vs NP progress

## Desired Features
### Agentic Research Loop
- [ ] **Planner**
    - [ ] Budget/time enforcement; task decomposition; milestone tracking
- [ ] **Conjecturer (LLM-assisted)**
    - [ ] Propose micro-lemmas/reductions; emit Lean stubs + SAT encodings
- [ ] **Counterexample Miner**
    - [ ] PySAT/SMT search; DRAT/LRAT logs; structure extraction for patterns
- [ ] **Formalizer (Lean 4)**
    - [ ] Prove parameterized statements; library for circuits/reductions/time bounds
- [ ] **Proof Critic (barrier-aware)**
    - [ ] Detects relativization/natural-proof patterns; suggests non-relativizing tweaks

### Exploratory Bets
- [ ] **A. Restricted-circuit lower bounds**
    - [ ] Monotone/formula/AC⁰ fragments → formal lower bounds
- [ ] **B. Algorithm synthesis with proofs**
    - [ ] Learn schema; **prove** polynomial bounds via recurrences/induction
- [ ] **C. Hardness-vs-randomness workbench**
    - [ ] Formalize micro-implications; correlate small circuits vs explicit functions
- [ ] **D. Barrier-aware reductions**
    - [ ] Design non-relativizing encodings; oracle-world diagnostics

### Infrastructure & Verification
- [ ] **Proof pipeline**
    - [ ] DRAT/LRAT logs + certified checker; Lean references to certificates
- [ ] **Reproducibility**
    - [ ] Devcontainer; ARM64/x86_64 images; pinned solver/tool versions
- [ ] **Budget control**
    - [ ] Unified cost meter; **auto-kill** at $100/month

## Design Requests
- [ ] **Repo layout**
    - [ ] `theory/` (Lean: circuits, reductions, complexity scaffolding)
    - [ ] `search/` (Python: agent supervisor, PySAT/SMT, circuit DSL)
    - [ ] `proofs/` (DRAT/LRAT artifacts, checker configs, hashes)
    - [ ] `infra/` (containers, CI, cost_guard.py)
    - [ ] `docs/` (papers, logs, barrier notes)
- [ ] **Make targets**
    - [ ] `setup`, `mine`, `check`, `bench`, `publish`

## Other Notes
- Start with tiny n to iterate quickly; only promote conjectures with **invariant** properties to Lean proofs.
- MIT license, CONTRIBUTING.md; LLM calls minimized + cached; local small models for boilerplate.
- Success metrics: new **proved** lower bounds (even restricted), new non-relativizing reductions, or tightened H↔R implications—each publishable and stepping stones toward a full resolution.
