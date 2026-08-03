# Postmortem: Bet A Monotone Parity Program (Vacuous Target)

Date closed: 2026-08-03
Disposition: archived to `archive/theory/Conjectures/BetA/` (bulk unversioned), supporting
modules archived to `archive/theory/Theory/` and `archive/theory/Tactics/`.

## What the program claimed

The flagship theorem V12 (`MonotoneParityInductive.lean`) stated:

    For all n >= 2, any monotone circuit computing parity on n inputs
    requires at least 2^(n/4) gates.

Supporting effort: 20+ LRAT-certified UNSAT results for "no monotone circuit with
max_gates <= g computes parity_n" (n = 2..16), plus a planned Razborov sunflower
inductive step for n >= 17.

## The flaw

The statement is vacuously true, and the entire empirical and formal program around
it certified a triviality.

- The synthesis encoder (`search/circuits/synthesis.py`) defines the monotone class
  as AND/OR gates over raw inputs, with no negations.
- Monotone circuits compute only monotone functions.
- Parity is not monotone for n >= 2: on inputs 10...0 and 11...0, raising the second
  bit flips parity from 1 to 0.
- Therefore no monotone circuit of any size computes parity. "Any monotone circuit
  computing parity needs >= 2^(n/4) gates" quantifies over an empty set. Every UNSAT
  certificate for every gate budget was guaranteed in advance by a three-line argument.
- Razborov's sunflower method proves lower bounds for functions that monotone circuits
  can compute at some size (CLIQUE, perfect matching). It does not apply to parity.
  The planned inductive step was proof engineering toward a misremembered theorem.

## What was real

- MC(MAJ_5) is 9 or 10 (majority is monotone; the g <= 8 UNSAT certificates and the
  g = 9 timeout are genuine, if microscopic, facts).
- AC0 depth-2 and depth-3 parity certificates for n = 4, 5 (real, but the asymptotic
  content has been known since Furst, Saxe, and Sipser 1984).

## Axiom debt (why green builds proved nothing)

The archived tree carried 7 axioms on the critical path plus 14 sorries:

- `sunflower_lemma` (Sunflower.lean)
- `lrat_implies_lower_bound` (Circuits.lean)
- `synthesis_encoding_correct`, `lrat_checker_sound` (EncodingCorrectness.lean)
- `tseitin_correct`, `lrat_soundness` (EncodingTactics.lean)
- `monotone_parity_hard` (CircuitTactics.lean)

In addition, `PvsNPGoal.lean` declared `InP` and `InNP` as opaque constants (using the
Lean 3 keyword `constant`, which does not compile on the v4.30.0 toolchain), making the
target `ClassP != ClassNP` formally unprovable: models exist where the two constants
coincide.

## Lessons (now enforced)

1. Non-vacuity check: before any lower-bound target is adopted, exhibit a positive
   witness that the function is computable in the class at some size (a SAT result at
   a larger budget). A lower bound over an empty set is not a result.
2. No axioms pretending to be theorems: the acceptance bar is zero sorries and axioms
   limited to propext, Classical.choice, Quot.sound (see docs/p-vs-np-proof-standards.md).
3. Formal targets must be real statements: no opaque constants standing in for
   complexity classes on the critical path.
