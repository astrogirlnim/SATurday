# R0: Resolution Foundations

Status: active
Lean home: theory/Theory/ProofComplexity/Resolution.lean

## Statement

Formalize in Lean, with zero sorries and standard axioms only:
1. Literals, clauses (finite sets of literals), CNF formulas (finite sets of
   clauses), assignments, evaluation.
2. Size-counted resolution derivations (so later rungs can state size bounds).
3. Soundness: if the empty clause is derivable from F, then F is unsatisfiable.
4. Refutational completeness: if F is unsatisfiable, the empty clause is derivable.

## Why this rung

Every later rung states bounds over these objects. Size-counted derivations are
required for R1's lower bound to be statable at all. This rung is also the pipeline
shakedown: prose, adversarial pass, formalization, axiom gate, session ledger.

## Falsification test

None (known mathematics). Risk is formalization cost only.

## Barrier notes

Not applicable (no lower-bound claim).

## Session log (append-only)

- 2026-08-03 reboot: rung adopted as active. Proof route chosen: soundness by
  induction on the derivation (case split on the resolved variable's value);
  completeness by Davis-Putnam variable elimination with induction on the number of
  variables, handling tautological clauses by a filtering lemma.
