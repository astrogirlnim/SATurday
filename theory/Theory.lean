import Theory.Basic
import Theory.ProofComplexity.Resolution
import Theory.ProofComplexity.PHP

/-!
# SATurday Theory Library

Main entry point for the SATurday formal verification library.

Reboot (2026-08-03): the library now targets the proof complexity ladder.
The old circuit, sunflower, and sheaf modules were archived to archive/theory
after the program audit; see docs/postmortems/ for the reasons.

## Modules
- `Theory.Basic`: fundamental smoke lemmas verifying the Lean setup
- `Theory.ProofComplexity.*`: the active ladder (resolution first)

Acceptance bar for anything imported here: compiles, zero sorries, and
axioms limited to propext, Classical.choice, Quot.sound
(enforced by scripts/check_axioms.sh).

LOG: Theory library root module for the proof complexity ladder
-/
