# P vs NP Proof Standards

These standards define what counts as an accepted result in this repo. They adopt
the bar set by the OpenAI ten-proofs release (2026-08-01): machine-checkable Lean
certificates with no unfinished goals and no nonstandard axioms.

## Acceptance bar (every accepted result)

- Formalized in Lean 4 and compiles under the pinned toolchain (theory/lean-toolchain).
- Zero sorries anywhere in the accepted declaration's dependency tree.
- Axioms limited to the three standard ones: propext, Classical.choice, Quot.sound.
  Enforced by scripts/check_axioms.sh, which runs lake build and checks
  print axioms output for every accepted declaration.
- No new axioms on the critical path, ever. External tool trust (SAT solvers, LRAT
  checkers) is never converted into a Lean axiom; empirical artifacts calibrate
  conjectures but are not proofs.
- Deterministic rerun: same inputs, same artifacts, same hashes.
- Every generated artifact is hash-addressed and reproducible locally.

## Frontier quarantine

- Work-in-progress statements live in namespaces ending in Frontier and may contain
  sorry. The axiom gate reports them separately. They are never cited as results,
  never imported by accepted modules, and never checked off on the solve checklist.

## Pipeline order (prose first, certify second)

- A proof attempt starts as a prose argument with an explicit gap list (prover).
- It passes an adversarial pass and a barrier audit before formalization effort is
  spent (barrier-auditor).
- Formalization (formalizer) converts an accepted prose argument into Lean meeting
  the acceptance bar above. A result exists only when the certificate exists.

## Statement hygiene

- Non-vacuity: every lower-bound statement must quantify over a provably nonempty
  set of objects (see docs/postmortems/bet-a-monotone-parity-vacuity.md).
- No opaque constants standing in for defined concepts on the critical path.
- Heuristic-only steps never justify theorem-level conclusions.
- All randomness-dependent empirical claims must be deterministic and replayable
  (fixed seeds, logged parameters).

## Minimum acceptance gate for the final claim

- Complete implication chain from base definitions to the final theorem, every link
  formalized (including the Cook-Reckhow bridge, rung R5).
- Independent internal red-team pass with no unresolved critical objections.
- Deterministic rerun reproducing the same proof artifacts.
