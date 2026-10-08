# R4: The Open Frontier

Status: active
Lean home: theory/Theory/ProofComplexity/AC0pFrege.lean (Frontier: AC0pFregeFrontier)

## Statement

A super-polynomial lower bound for a propositional proof system with no known
super-polynomial lower bounds. Ordered subtargets:

1. AC0[p]-Frege: bounded-depth Frege with mod-p counting gates. Open since the late
   1980s although the circuit analogue (Razborov-Smolensky) is known. Candidate hard
   families: Count(q) principles against mod q' reasoning, Tseitin over expanders.
2. TC0-Frege.
3. Frege.
4. Extended Frege.

## Why this rung

This is the research frontier where new mathematics is required. Everything below
it is training and machinery; everything above it is the summit.

## Falsification tests

T4.1: for each candidate family and system, literature check plus bounded empirical
search for short proofs in simulable fragments; quasi-polynomial upper bounds kill
the family for that rung.
T4.2: every proposed argument names the proof-system property it exploits and
passes the barrier audit before formalization effort is spent.

## Barrier notes (the real walls)

- Interpolation unavailable (dies below this level).
- Krajicek generators and Razborov conjectures: strong-system lower bounds may
  require breaking cryptographic assumptions; every candidate argument must state
  why it does not implicitly construct a distinguisher for a standard pseudorandom
  object.
- Simulation order: an AC0[p]-Frege bound says nothing about TC0-Frege and above;
  each subtarget is its own wall.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed. No active candidate argument. Prose search
  begins after R1 certification; empirical calibration may start earlier.
- 2026-10-08 adopt (operator "go"): first subtarget AC0[p] Frege. Lean surface certified
  in AC0pFrege.lean: formulas with MOD_p connectives (`Fm`), a dag like sequent calculus with
  MOD_p defining axioms (`FRefutes p d F L`), soundness (`frefutes_unsat`), and the non
  vacuity witness: every unsatisfiable CNF has a depth one refutation, by simulating
  resolution (`frefutes_of_unsat`). Locked target: `AC0pFregeFrontier.r4_target :
  ∀ p prime, AC0pFregeLB p` (some polynomial size unsatisfiable family needs super
  polynomial size refutations at every fixed depth). Primary candidate families: Tseitin
  mod q on expanders (q ≠ p), Count_q, onto PHP, random k CNF.
  Kill conditions: (T4.1) a quasi polynomial size AC0[p] Frege refutation of a candidate
  family kills that family; (T4.2) an argument that would also separate systems known
  to be equal, give a lower bound for a system with known short proofs of the family, or
  break a standard pseudorandom generator assumption fails the barrier audit. Three failed
  attempts on one method kill that method branch.
  Plan and checklist: docs/ladder/r4-research-plan.md, docs/ladder/r4-completion-checklist.md.
