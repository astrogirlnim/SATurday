# R3: One Certified Bound Above Resolution

Status: proposed
Lean home: theory/Theory/ProofComplexity/ (module split decided at adoption)

## Statement

One certified super-polynomial lower bound for a system strictly stronger than
resolution. Candidates, to be selected by prover cycles on formalization cost and
technique reuse toward R4:

1. Res(k) (resolution over k-DNFs) lower bounds.
2. Cutting planes lower bounds via feasible interpolation (Pudlak 1997) for
   clique-coloring formulas.
3. Bounded-depth Frege lower bounds for PHP (Ajtai; Pitassi-Beame-Impagliazzo;
   Krajicek-Pudlak-Woods).

## Why this rung

First step above resolution. Each candidate exercises a technique class
(k-DNF switching, interpolation, restriction-based depth reduction) whose reach and
walls must be understood before R4 work is credible.

## Falsification test

Per candidate family: empirical proof-size calibration where a solver-checkable
fragment exists; literature check for upper bounds killing the family.

## Barrier notes

Interpolation is known to die above this level (Bonet-Pitassi-Raz for TC0-Frege
under factoring hardness; Krajicek-Pudlak for extended Frege under RSA); an
interpolation-based R3 result must be documented as non-extendable, acceptable for
R3 but not as the R4 plan.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed.
