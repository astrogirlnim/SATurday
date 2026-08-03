# P vs NP Stop Conditions

Hard stop conditions for invalid research directions and runaway work.

## Direction validity

- Stop if the direction requires any new unproven axiom on the critical path.
- Stop if a required step cannot be formalized in Lean-level statements.
- Stop if the applicable barrier or limitative-result checklist
  (docs/p-vs-np-barrier-evasion.md) has no concrete evasion argument.
- Stop if a key implication is only heuristic and has no formal reduction.
- Stop if the direction fails an explicit adversarial counterexample attempt 3 times.
- Stop if deterministic rerun does not reproduce core artifacts.
- Stop if the direction no longer connects to the locked target chain
  (proof system lower bounds to NP != coNP to P != NP).

## Statement validity

- Stop if a lower-bound target is vacuous: the quantified set of objects is empty
  (example: monotone circuits computing a non-monotone function). Every lower-bound
  rung requires a recorded non-vacuity witness before mining or proving begins.
- Stop if a proposed lock contradicts recorded falsification evidence.

## Resource budgets (fixes the 15-hour CNF incident of 2026-06-02)

- Every solver or generation run must be preceded by a recorded cost estimate:
  variable count, clause count, estimated CNF bytes, and projected wall-clock time.
- Hard caps per session action, enforced by the tooling, not by intent:
  - CNF generation: refuse to start if estimated CNF exceeds 500 MB.
  - Solver wall clock: default cap 1800 seconds per instance, 3600 seconds per
    session action; overridable only by an explicit config value recorded in the
    session log.
  - Any breach kills the run, records a timeout artifact, and ends the action.
- A session never leaves a solver running past the session end.

## Session discipline

- One session, one action, one canonical state write (unchanged from the saturday
  contract).
- If an action is blocked twice for the same cause, the next session must either
  change approach or record a kill decision; grinding the same blocked action a
  third time is a stop violation.
