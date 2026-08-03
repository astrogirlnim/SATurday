# R1: PHP Haken Lower Bound

Status: proposed
Lean home: theory/Theory/ProofComplexity/PHP.lean

## Statement

There is a constant c > 1 such that for all sufficiently large n, every resolution
refutation of PHP(n+1, n) (pigeonhole: n+1 pigeons, n holes) has size at least c^n.
Statement lives in a Frontier namespace until proved.

## Why this rung

First genuine certified lower bound of the program. Haken 1985 is the founding
result of proof complexity; formalizing it validates that the ladder can certify
lower bounds, not just definitions.

## Non-vacuity witness

PHP(n+1, n) is unsatisfiable (pigeonhole principle), and refutational completeness
(R0) guarantees resolution refutations exist; the lower bound quantifies over a
nonempty set. Recorded per the Bet A postmortem rule.

## Candidate routes

1. Ben-Sasson-Wigderson width method: prove the width-size relation, then a width
   lower bound for PHP. Pulls R2 machinery forward; likely the cleaner Lean path.
2. Haken's original bottleneck counting. More self-contained, heavier combinatorics.

## Falsification test

T1.1: falsifier runs PHP(n+1, n) for growing n under budget caps and records proof
sizes from a real solver. Expected: super-polynomial growth curve. A polynomial fit
over a wide range would signal a mis-stated target (it will not happen; this is the
calibration discipline, not genuine doubt about Haken).

## Barrier notes

Resolution lower bounds face no applicable wall (interpolation works here;
automatability irrelevant to lower bounds). Simulation sandwich: resolution is
simulated by Res(k), cutting planes, and Frege; the bound transfers to nothing
above it.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed. Opens when R0 is certified.
