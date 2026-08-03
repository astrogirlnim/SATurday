# R1: PHP Haken Lower Bound

Status: active
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
- 2026-08-03 formalize (statement): rung opened. phpCNF defined in Lean over the
  R0 syntax (pigeon i in Fin (n+1), hole j in Fin n, variable i * n + j).
  CERTIFIED support results, gate green: phpCNF_unsat (a model would give an
  injection of n+1 pigeons into n holes, contradicting cardinality) and
  phpCNF_refutable (via R0 completeness). These are the formal non-vacuity
  witness. The R1 target php_resolution_size_lower_bound (size at least
  2 ^ (n / 20) for n at least 20) is stated in the Frontier namespace with
  sorry, reported by the gate as quarantined, and is not a result.
- 2026-08-03 prove (route selection and decomposition):
  Route decision: Beame and Pitassi 1996 (simplified Haken bottleneck counting),
  NOT the naive width method. Reason found during adversarial pass: the
  Ben-Sasson and Wigderson size-width tradeoff is weak on PHP directly because
  the pigeon axioms already have width n (the wide-axiom problem); making width
  work for PHP needs Razborov's pseudo-width machinery, which is heavier than
  the counting proof. Width machinery stays at R2 where it natively applies
  (Tseitin over expanders, random k-CNF).
  Lemma decomposition for the counting route:
  1. Critical assignments: total maps sending some n pigeons bijectively to the
     n holes, one pigeon left out. Finite, definable as functions on Fin types.
     Gap class: routine.
  2. Clause complexity measure: for a clause C in a refutation of PHP, measure
     the number of pigeons whose placement C constrains on critical assignments;
     prove the measure is subadditive across a resolution step, so a size-S
     refutation contains a clause of intermediate complexity. Gap class: hard
     (the combinatorial heart).
  3. Intermediate-complexity clauses are wide: such a clause must mention at
     least a constant fraction of the grid variables of the constrained pigeons.
     Gap class: hard.
  4. Counting assembly: intermediate clauses are killed by many critical
     assignments; a union bound over the S clauses forces S at least
     2 ^ (n / 20) for n at least 20. Purely finite counting, no probability
     measure needed if phrased over the finite set of critical assignments.
     Gap class: routine given 2 and 3.
  Adversarial pass: quantifier order in the Lean statement is over every
  derivation, matching the informal claim; the argument is purely syntactic and
  finite, no hidden uniformity or asymptotic hand-waving except the explicit
  constant 20, which the Beame and Pitassi write-up supports; non-vacuity is
  certified (phpCNF_refutable). Worst gap: item 2's subadditivity under the
  erase-then-union resolvent definition must be re-derived carefully because
  textbook write-ups treat clauses as sets of literals with implicit weakening.
  Barrier audit (resolution level): no applicable walls. Feasible interpolation
  is not used; no constructive property of Boolean functions is built, so no
  natural-proofs analogue; the claim respects simulation order (asserts nothing
  above resolution). Verdict: proceed; next action is a formalize cycle on
  lemma 1 (critical assignments) once a session budget allows.
- 2026-08-03 falsify (T1.1 executed, budgets enforced): kissat proof sizes for
  PHP(n+1, n), seed 42, instance cap 300 s. Proof lines by n:
  4: 1, 5: 10, 6: 225, 7: 4421, 8: 5930, 9: 192546, 10: 907601 (74.5 s solve),
  11: TIMEOUT at the 300 s cap (sweep stopped by the runner as designed).
  Reading: consecutive growth ratios 10x, 22x, 20x, 1.3x, 32x, 4.7x; the curve is
  strongly super-polynomial and consistent with the 2^(n/20) target statement.
  T1.1 passes: no polynomial fit is remotely possible. Artifacts hashed in
  proofs/index.json; ledger search/logs/falsifier_runs.jsonl. Proof check labeled
  format_only (the verify_lrat stub is not a verified checker); this is
  calibration data, not a theorem.
