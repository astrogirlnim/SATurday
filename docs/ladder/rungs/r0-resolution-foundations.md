# R0: Resolution Foundations

Status: certified
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
- 2026-08-03 formalize: CERTIFIED. theory/Theory/ProofComplexity/Resolution.lean
  compiles with zero sorries; scripts/check_axioms.sh reports exactly propext,
  Classical.choice, Quot.sound for derivation_entails, resolution_sound,
  resolution_complete, resolution_refutable_iff. One proof improvement over the
  planned route: no tautology filtering lemma was needed. The Davis-Putnam split
  was made polarity strict (posClauses and negClauses each demand the opposite
  literal absent), so clauses containing both polarities of the eliminated
  variable drop out of the elimination and never block the extension argument.
  Size-counted derivations (Derivation.size) are in place for the R1 statement.
  Most important thing learned: the mathlib rename to notMem style names is the
  only friction point at this toolchain version; the AppleDouble sidecar files on
  this external drive break lake module globbing and must be cleaned before every
  build (the axiom gate now does this).
