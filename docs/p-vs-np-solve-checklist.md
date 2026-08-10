# P vs NP Solve Checklist

Target: a complete, correct proof that `P != NP` or `P = NP`, with machine-checkable
core arguments. Reboot of 2026-08-03: main attack relocked to the proof complexity
ladder after the program audit (see docs/postmortems/).

## 0) Lock Problem Statement
- [x] Fix exact target chain: proof system lower bounds -> NP != coNP -> P != NP
      (`P != NP` primary, `P = NP` secondary branch via a poly-bounded proof system).
- [x] Fix accepted proof standards (zero sorries, standard axioms only, axiom gate).
- [x] Fix stop conditions (barrier failure, vacuous statements, budget breaches).
- [ ] Formalize the target chain statement in Lean without opaque constants (rung R5;
      Encoding and Complexity defs certified 2026-08-10; Frontier: nonvacuity,
      Psubseteq NP, bridge theorems, FormulaEncoding).

## 1) Pick One Main Attack
- [x] Choose one primary framework only: proof complexity ladder.
- [x] Write a one-line falsifiable claim (docs/p-vs-np-main-attack.md).
- [x] Freeze all non-primary directions until pass or fail evidence appears.

## 2) Barrier Evasion Requirements
- [x] State how the attack relates to relativization.
- [x] State how the attack relates to natural proofs.
- [x] State how the attack relates to algebraization.
- [x] Record the ladder-specific walls (interpolation death, non-automatability,
      simulation order) and the per-rung audit rule.

## 3) Build the Core Lemma Chain
- [x] Define the minimum rung sequence R0 to R5 (docs/p-vs-np-lemma-chain.md).
- [x] Mark each rung as: known, adaptation, or new.
- [x] For each new rung, add one immediate falsification test.
- [x] Eliminate any rung that cannot be made precise in Lean-level terms.

## 4) Formalization First
- [x] R0: resolution soundness and completeness in Lean, zero sorries, gate passes.
- [x] R1 statement: PHP family and the Haken lower bound stated in Lean
      (Frontier namespace until proved); non-vacuity witness phpCNF_unsat and
      phpCNF_refutable certified.
- [x] Prove the first nontrivial new lemma in Lean without new axioms
      (exists_intermediate_pigeonComplexity and the linear size bound).
- [x] R1 certified (honest exponential): php_resolution_size_lower_bound at
      2^((n-3n/4-36)/35) for n≥288; paper 2^(n/20) not claimed; R2 and R5 opened.
- [ ] Keep a hard rule: no paper-only dependency may sit on the critical path.

## 5) Adversarial Validation Loop
- [x] Barrier audit run against the first R1 prose argument (recorded in
      docs/ladder/rungs/r1-php-haken.md; verdict proceed).
- [x] Falsifier baseline: PHP, Tseitin, random k-CNF proof-size curves recorded
      under budget caps (search/logs/falsifier_runs.jsonl; PHP wall at n=11).
- [ ] If a blocker survives 3 attempts, refactor or kill the branch.

## 6) Convergence Criteria
- [ ] Show a complete implication chain from base definitions to final theorem.
- [ ] Verify every nontrivial step is formalized or reduced to already formalized
      results.
- [ ] Produce a minimal trusted core that can be independently rechecked.
- [ ] Run full reproducibility: same artifacts, same outputs, deterministic rerun.

## 7) Final Proof Readiness
- [ ] Independent internal red-team review of the full argument.
- [ ] Resolve all critical objections or formally scope remaining assumptions.
- [ ] Freeze theorem statement and proof artifacts.
- [ ] Publish final machine-checkable package.

## Weekly Execution Cadence
- [ ] 1 primary theorem target per week.
- [ ] 1 go or no-go branch decision per week.
- [ ] 1 formalization milestone per week.
- [ ] 1 barrier audit update per week.
