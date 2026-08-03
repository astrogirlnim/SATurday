# P vs NP Solve Checklist

Target: a complete, correct proof that `P != NP` or `P = NP`, with machine-checkable core arguments.

## 0) Lock Problem Statement
- [x] Fix exact target statement in Lean (`P != NP` primary, `P = NP` secondary branch).
- [x] Fix accepted proof standards (no unproven external assumptions, no heuristic leaps).
- [x] Fix stop conditions for invalid directions (barrier failure, contradiction, non-formalizable step).

## 1) Pick One Main Attack
- [x] Choose one primary framework only (circuit lower bounds, proof complexity, algebraic, geometric, or logic).
- [x] Write a one-line falsifiable claim for this framework.
- [x] Freeze all non-primary directions until pass/fail evidence appears.

## 2) Barrier Evasion Requirements
- [x] State how the attack evades relativization.
- [x] State how the attack evades natural proofs.
- [x] State how the attack evades algebraization.
- [x] Reject the attack if any evasion argument is missing or circular.

## 3) Build the Core Lemma Chain
- [x] Define the minimum lemma sequence that implies the final theorem.
- [x] Mark each lemma as: known, adaptation, or new.
- [x] For each new lemma, add one immediate falsification test.
- [x] Eliminate any lemma that cannot be made precise in Lean-level terms.

## 4) Formalization First
- [ ] Encode all definitions for the main attack in Lean before deep expansion.
- [ ] Prove the first nontrivial new lemma in Lean without new axioms.
- [ ] Prove one composition step where two new lemmas combine.
- [ ] Keep a hard rule: no “paper-only” dependency may sit on the critical path.

## 5) Adversarial Validation Loop
- [ ] Run explicit skeptic checks for hidden assumptions and quantifier errors.
- [ ] Search for oracle-style counterworld failures against each major lemma.
- [ ] Run SAT/complexity stress tests where relevant to detect false intuitions.
- [ ] If a blocker survives 3 attempts, either refactor or kill the branch.

## 6) Convergence Criteria
- [ ] Show a complete implication chain from base definitions to final theorem.
- [ ] Verify every nontrivial step is formalized or reduced to already formalized results.
- [ ] Produce a minimal trusted core that can be independently rechecked.
- [ ] Run full reproducibility: same artifacts, same outputs, deterministic rerun.

## 7) Final Proof Readiness
- [ ] Independent internal red-team review of the full argument.
- [ ] Resolve all critical objections or formally scope remaining assumptions.
- [ ] Freeze theorem statement and proof artifacts.
- [ ] Publish final machine-checkable package.

## Weekly Execution Cadence
- [ ] 1 primary theorem target per week.
- [ ] 1 go/no-go branch decision per week.
- [ ] 1 formalization milestone per week.
- [ ] 1 barrier audit update per week.
