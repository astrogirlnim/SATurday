# R5: Cook-Reckhow Bridge

Status: proposed
Lean home: theory/Theory/ProofComplexity/Bridge/ (created at adoption)

## Statement

Formalize in Lean, zero sorries, standard axioms only:

1. P and NP over a real machine model. Base: mathlib computability
   (Turing.TM2ComputableInPolyTime as the polynomial-time notion; NP via
   polynomial-time verifiers with polynomially bounded witnesses). coNP as
   complements.
2. Propositional proof systems (Cook-Reckhow): polynomial-time computable onto maps
   from strings to TAUT (equivalently UNSAT refutation systems).
3. Bridge theorem 1: a polynomially bounded proof system exists iff NP = coNP.
4. Bridge theorem 2: P = NP implies NP = coNP.
5. Corollary (summit shape): if every propositional proof system has a
   super-polynomially hard family, then P != NP.

## Why this rung

This replaces the vacuous opaque-constant PvsNPGoal module (archived) with a real
target statement. Until R5 is certified, the summit link is informal and cited, and
is never encoded as an axiom.

## Falsification test

None (known mathematics). Risk is formalization cost: mathlib's complexity-theory
layer is thin, and encoding-invariance work is substantial. This is why R5 is
deferred until R1 proves the pipeline can certify hard content.

## Barrier notes

Not applicable (no lower-bound claim).

## Session log (append-only)

- 2026-08-03 reboot: rung proposed. Opens when R1 is certified.
