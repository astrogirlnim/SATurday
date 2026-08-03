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
- 2026-08-03 tooling upgrade (real proof checking): drat-trim built at
  infra/build/drat-trim and wired into search/bin/verify_lrat, which now
  decompresses gzip inputs and passes only on an explicit s VERIFIED line.
  Two corrections to the earlier falsify entry: the proofs kissat emits are
  binary DRAT (the .lrat extension is historical), so the proof lines metric in
  that entry counted lines of binary data and should be read as rough size
  only; the honest metric is drat-trim core lemmas and resolution steps, now
  recorded per instance in search/logs/falsifier_runs.jsonl. Reverified today:
  PHP core lemmas grow 7 (n=3), 31 (n=4), 143 (n=5), 1026 (n=6), and 488949
  with 10.5 million resolution steps at n=9 (checked in 4.5 seconds). The
  exponential reading of T1.1 stands, now on verified numbers. A corrupted
  proof was confirmed to fail the checker (negative control, test file
  deleted).
- 2026-08-03 formalize (BP96 lemma 1: critical assignments): CERTIFIED, gate
  green on 7 new declarations in
  theory/Theory/ProofComplexity/CriticalAssignments.lean. Encoding decision:
  a critical assignment is carried by a permutation pi of Fin (n+1); pigeon i
  sits in hole j exactly when pi i equals Fin.castSucc j, and the left-out
  pigeon is pi.symm (Fin.last n). This avoids subtype bijections entirely.
  Certified: pvar_inj (variable encoding injective via division and remainder),
  criticalAssignment_pvar (grid specification), criticalAssignment_sat_holeClause
  (permutation injectivity means no shared holes),
  criticalAssignment_sat_pigeonClause_iff (satisfied exactly when placed),
  criticalAssignment_falsifies_leftOut, criticalAssignment_sat_iff (a critical
  assignment falsifies exactly one clause of PHP, the left-out pigeon clause),
  criticalAssignment_sat_php_erase (the BP96 launching shape). Three build
  attempts used (within the formalizer contract): attempt failures were Nat
  division lemma name drift, fixed with toolchain-exact names
  (Nat.mul_add_mod_of_lt, Nat.mul_add_div). One tooling fix landed alongside:
  the axiom gate parser now merges wrapped print axioms output lines, which
  long declaration names triggered for the first time.
  Most important thing learned: the C-as-clause phrasing of
  criticalAssignment_sat_iff (quantifying over the clause, not the pigeon
  index) sidesteps pigeon clause collision edge cases at n equals 0, so no
  side conditions were needed anywhere in the module.
  Next: lemma 2 of the decomposition, the clause complexity measure and its
  subadditivity across a resolution step (the combinatorial heart; prove cycle
  first to pin the measure definition against the erase-then-union resolvent).
- 2026-08-03 human gate merge_certified: CriticalAssignments.lean accepted into
  the accepted tree. Seven declarations remain listed in
  scripts/accepted_declarations.txt; axiom gate rechecked green; module has no
  Frontier namespace and no sorry. R1 status stays active (support lemmas only;
  the Haken size bound itself is still Frontier).
- 2026-08-03 prove (BP96 lemma 2: clause complexity measure and subadditivity):

  Restated target for this lemma only: define a complexity measure μ on clauses
  of PHP(n+1, n) that is (i) zero on every hole clause, (ii) exactly n! on each
  pigeon clause, (iii) exactly (n+1)! on the empty clause, and (iv) subadditive
  across our erase then union resolvent, so that for every resolution step
  μ(resolvent C D x) ≤ μ(C) + μ(D).

  Non vacuity: Crit(n) is the finite set of permutations of Fin (n+1), size
  (n+1)!, and criticalAssignment n π is certified for each π; the empty clause
  is never satisfied, so the measure on the empty clause is nonempty.

  Definition chosen (one of three sketches; developed):
  Let Crit(n) := Equiv.Perm (Fin (n+1)).
  Let Fals(C) := { π ∈ Crit(n) | ¬ clauseSat (criticalAssignment n π) C }.
  Let μ(C) := |Fals(C)|.

  Rejected alternatives for this cycle:
  (A) L(C) := set of left out pigeons i for which some π with leftOut π = i
  falsifies C. Gives L(∅) = all n+1 pigeons and L(pigeon i) = {i}, with
  L(resolvent) ⊆ L(C) ∪ L(D), but only yields a linear size lower bound S ≥ n+1
  after leaf summing, so it is too weak as the sole measure for the exponential
  claim (keep it as an auxiliary later if useful).
  (B) Minimum support size among pigeons mentioned by literals of C. Easy to
  define from syntax, but subadditivity under resolvent fails or needs weakening
  clauses; textbook writeups that use it silently allow weakening.

  Developed argument for μ = |Fals|:

  Claim 1 (axioms). For every hole clause H ∈ holeClauses n, Fals(H) = ∅, so
  μ(H) = 0. Proof: criticalAssignment_sat_holeClause (certified).
  For pigeonClause n i, Fals(pigeonClause n i) = { π | π.symm (Fin.last n) = i },
  so μ = n!. Proof: criticalAssignment_sat_pigeonClause_iff plus the fact that
  π.symm last runs through all pigeons equally often (exactly n! each).
  For the empty clause, Fals(∅) = Crit(n), so μ(∅) = (n+1)!. Proof: clauseSat
  of empty is ∃ l ∈ ∅, ..., which is false for every assignment.

  Claim 2 (subadditivity under erase then union). For any C, D and variable x
  with ⟨x, true⟩ ∈ C and ⟨x, false⟩ ∈ D,
  Fals(resolvent C D x) ⊆ Fals(C) ∪ Fals(D), hence μ(resolvent C D x) ≤ μ(C) + μ(D).
  Proof. Fix π and write α := criticalAssignment n π. Suppose α satisfies both
  C and D; we show α satisfies the resolvent. Same case split as
  derivation_entails (R0, certified):
  if α x = true then the negative literal of x is false under α, so the witness
  literal of D is not ⟨x, false⟩ and therefore survives in D.erase ⟨x, false⟩,
  hence sits in the resolvent;
  if α x = false then the witness of C is not ⟨x, true⟩ and survives in
  C.erase ⟨x, true⟩.
  Contrapositively, if α falsifies the resolvent then α falsifies C or D.

  Claim 3 (leaf sum, honesty). By induction on Derivation, μ(conclusion) ≤
  sum of μ over hyp leaves of the derivation tree. Every PHP hyp leaf has
  μ ≤ n!, and the number of hyp leaves is at most Derivation.size. Therefore
  (n+1)! = μ(∅) ≤ S · n!, so S ≥ n+1. This is only a linear lower bound.
  Lemma 2 alone does NOT prove the exponential R1 target; the exponential
  content lives in lemmas 3 and 4 (intermediate complexity plus width).

  Gap list:
  G1. Formalizing Fals and μ as Finset valued objects over Equiv.Perm, with
  decidable membership via criticalAssignment (decide already used there).
  Class: routine.
  G2. Claim 1 for pigeon clauses: counting that exactly n! permutations leave
  out a fixed pigeon (bijection with Equiv.Perm (Fin n) after removing the
  left out element). Class: routine (mathlib Equiv.Perm card facts).
  G3. Claim 2 written against our exact resolvent definition, including the
  case where C still contains ⟨x, false⟩ after erase of ⟨x, true⟩ (allowed by
  our Derivation; soundness still holds). Class: routine given R0 case split;
  mark hard only if Lean encoding of "witness survives erase" gets sticky.
  G4. Honest separation: do not claim exponential from Claim 3. Class: none
  (discipline, already recorded).

  Self adversarial pass:
  Quantifiers: μ is defined for every clause, subadditivity for every legal
  resolution step; the R1 target still quantifies over every Derivation of
  empty from phpCNF n. No hidden asymptotic: Claim 3 is exact for every n ≥ 1
  (for n = 0, Fin 0 is empty and hole clauses vanish; the module already
  handles n = 0 in lemma 1). Off by one: (n+1)! / n! = n+1 is correct for the
  linear bound. Does this secretly prove something false? No; linear resolution
  lower bounds for PHP are true and weak. Does the erase then union silently
  break subadditivity? The case analysis mirrors certified derivation_entails,
  so a failure here would already contradict R0 soundness. Worst remaining gap
  for the exponential program is NOT in lemma 2; it is lemma 3 (a clause with
  medium μ must be wide in grid literals), which needs a separate prove cycle.

  Status: partial (lemma 2 pinned with only routine gaps; exponential content
  deferred). Next recommended action: formalize Claims 1 to 3 for μ, then a
  fresh prove cycle for lemma 3 (width of medium complexity clauses).
- 2026-08-03 formalize (BP96 lemma 2: clause complexity): CERTIFIED, gate green
  on 13 new declarations in
  theory/Theory/ProofComplexity/ClauseComplexity.lean. Definitions: Crit,
  falsifies, Fals, complexity (= μ). Claim 1: complexity_empty = (n+1)!,
  complexity_holeClause = 0, complexity_pigeonClause = n! (via card_perm_fiber:
  evaluation fibers of Perm partition equally). Claim 2:
  Fals_resolvent_subset and complexity_resolvent_le under erase then union.
  Claim 3: leaf complexitySum, complexity_le_complexitySum, and
  php_resolution_size_linear (every refutation has size ≥ n+1). Honest: this
  is only the linear bound; exponential R1 still needs lemmas 3 and 4.
  Most important thing learned: Classical was required for Finset.filter over
  falsifies (clauseSat is existential); the module is noncomputable but axiom
  clean. Next: prove cycle for lemma 3 (medium μ clauses are wide).
- 2026-08-03 human gate merge_certified: ClauseComplexity.lean accepted into
  the accepted tree. Thirteen declarations remain in
  scripts/accepted_declarations.txt; gate green; no Frontier and no sorry.
  R1 stays active. Linear bound php_resolution_size_linear is now an accepted
  result (not the exponential target).
- 2026-08-03 prove (BP96 lemma 3: width of medium complexity): PARTIAL, with a
  critical adversarial correction to the lemma statement itself.

  Restated naive target (from the earlier decomposition): every clause C with
  μ(C) at least (n+1)! / 2^{δ n} contains at least δ n literals.

  Non vacuity: Crit(n) and μ are certified (ClauseComplexity).

  Adversarial pass (kills the naive target): take C = {⟨pvar 0 0, true⟩}, a
  single positive literal (width 1). Then α falsifies C iff π does not place
  pigeon 0 in hole 0, so μ(C) = (n+1)! − n! which is at least (n+1)! / 2 for
  n ≥ 1. The naive "large μ implies wide" statement is FALSE for our μ.

  Rejected patches:
  (A) L*(C) = {i | every π leaving out i falsifies C}. Gives |L*(∅)| = n+1 and
  |L*(pigeon i)| = 1, but nonempty non axiom clauses appear to have |L*| ≤ 1,
  so L* cannot carry intermediate complexity for the exponential argument.
  (B) Keep naive μ and restrict to "bottleneck" clauses (first falsified on a
  root to leaf walk). Still needs a width law that survives the positive
  literal counterexample; not pinned this cycle.

  Developed pivot (one argument, adaptation of Beame and Pitassi 1996 /
  Haken bottleneck counting, not a new theorem):
  The exponential content is not a pure width law for μ. It is an incidence
  counting argument: pairs (π, C) where C is a designated bottleneck clause
  for π in a size S refutation, combined with a structural bound on how many
  critical assignments a clause of small "matching complexity" can own.
  Matching complexity (literature adaptation, to be locked next): the size of
  the largest partial matching M of pigeons to holes such that every critical
  extension of M falsifies C. Single positive literals have matching
  complexity 0 or 1 and do not contradict the literature width law for that
  measure. Our μ remains the right leaf to root potential for Claim 3 of
  lemma 2 (linear bound, certified); it is the wrong sole measure for lemma 3.

  Gap list:
  G1. Literal level characterization of falsifies (needed for any repaired
  lemma 3): π falsifies C iff every literal of C is false under
  criticalAssignment n π; positive ⟨pvar i j, true⟩ is false iff π i ≠
  castSucc j; negative ⟨pvar i j, false⟩ is false iff π i = castSucc j.
  Class: routine. Formalize this cycle.
  G2. Corollary μ({positive p_ij}) = (n+1)! − n!, recording the counterexample
  as a certified theorem so the naive lemma cannot silently return. Class:
  routine.
  G3. Lock the precise literature statement of matching complexity (or the
  exact BP96 lemma number and formula) against Beame and Pitassi 1996 before
  further prove cycles on lemma 3. Class: hard (scholarship, not Lean).
  G4. Exponential assembly (old lemma 4) waits on G3. Class: hard.

  Self adversarial pass: the pivot does not claim a new lower bound; it
  refuses to formalize a false width lemma. Quantifiers on G1 and G2 are
  explicit and finite. No barrier issue at resolution level. Worst gap: G3
  must be settled by reading BP96 and writing a one line falsifiable claim
  before the next prove cycle on lemma 3 proper.

  Status: partial. Next: formalize G1 and G2 (literal characterization and
  the width 1 counterexample theorem), then a scholarship prove cycle to lock
  the matching complexity statement from BP96.
- 2026-08-03 formalize (lemma 3 support G1/G2): SUCCESS. Extended
  ClauseComplexity.lean with litUnsat_pos_iff, litUnsat_neg_iff,
  falsifies_iff_forall_lit, complexity_singleton_pos. Gate green
  (scripts/check_axioms.sh). Seventeen declarations listed for this module
  cluster (thirteen prior plus four new). No Frontier and no sorry in the
  accepted tree. Certified that μ({p_ij}) = (n+1)! − n!, so the naive width
  lemma stays dead. Pending human gate merge_certified. Next: prove cycle to
  lock the BP96 matching complexity statement (G3), then resume lemma 3.
- 2026-08-03 human gate merge_certified: the four lemma 3 support declarations
  (litUnsat_pos_iff, litUnsat_neg_iff, falsifies_iff_forall_lit,
  complexity_singleton_pos) accepted into the accepted tree. Gate remains
  green. R1 stays active. Next: prove cycle locking BP96 Lemma 1 complexity.
- 2026-08-03 prove (G3 lock: BP96 Lemma 1 complexity, not matching measure):
  SUCCESS on scholarship lock; PARTIAL on the width argument (gaps for
  formalize).

  Literature source (known): Beame and Pitassi, Simplified and Improved
  Resolution Lower Bounds, FOCS 1996, Lemma 1 and Theorem 2. PDF:
  https://homes.cs.washington.edu/~beame/papers/focsclause.pdf

  Locked definition (adaptation to our PHP(n+1, n) encoding; known measure,
  not new):
    L(C) := { i : Fin (n+1) | ∃ π : Crit n, π i = Fin.last n ∧ falsifies n C π }
    comp(C) := |L(C)|
  Equivalent BP96 phrasing: minimum number of pigeon axioms that imply C on
  all critical assignments. Equivalence: a critical assignment falsifies
  exactly the left out pigeon axiom, so S implies C on critical assignments
  iff L(C) ⊆ indices(S), hence the minimum |S| equals |L(C)|.

  Values:
    comp(∅) = n+1
    comp(pigeonClause i) = 1
    comp(holeClause) = 0
  Subadditivity: L(resolvent C D x) ⊆ L(C) ∪ L(D), so
    comp(resolvent) ≤ comp(C) + comp(D).
  Intermediate clause (from subadditivity and leaf values): every refutation
  contains a clause C with (n+1)/3 < comp(C) ≤ 2(n+1)/3.

  Adversarial reconciliation with the width 1 counterexample: for
  C = {⟨pvar 0 0, true⟩}, every left out pigeon admits some π falsifying C,
  so comp(C) = n+1, which lies outside the intermediate band
  ((n+1)/3, 2(n+1)/3]. The naive μ measure put this C in the "large" class;
  comp correctly classifies it as near empty complexity. Prior "matching
  complexity" pivot is REJECTED; μ stays for the certified linear bound only.

  Lemma 3 restated (adaptation of BP96 Lemma 1, one developed argument):
  Let C be a clause with m = comp(C) and (n+1)/3 < m ≤ 2(n+1)/3. After the
  Buss monotone transform (replace each ¬p_{i,k} by the positive literals
  {p_{t,k} | t ≠ i}, which preserves critical satisfaction), C contains at
  least (n+1 − m)·m distinct positive grid literals. For m in the intermediate
  band this is at least 2(n+1)²/9. Proof idea (BP96): take minimal S = L(C)
  with |S| = m; fix i ∈ S and an i-critical α falsifying C; for each pigeon
  j ∉ S, the j-critical α' obtained by swapping i with j satisfies C (because
  left out j ∉ S means α' satisfies all of S, hence C); monotone C must
  contain the positive variable that distinguishes α from α'.

  Size assembly (BP96 Theorem 2, deferred as lemma 4): if S < 2^{n/20}, a
  short sequence of matching restrictions kills every clause of size ≥ n²/10,
  leaving a refutation of a still nontrivial PHP with no large clause,
  contradicting Lemma 1. Constant 20 matches our Frontier statement.

  Gap list:
  G1/G2. Done (certified).
  G3. LOCKED this cycle: comp = |L|, intermediate band, reject matching
  measure. Class: closed.
  G5. Formalize L, comp, values, subadditivity, intermediate existence.
  Class: routine to medium (Finset image of left outs over Fals).
  G6. Formalize monotone transform and the (n+1−m)m width lower bound for
  intermediate comp. Class: hard (the BP96 swap argument).
  G7. Restriction size assembly (lemma 4 / Theorem 2). Class: hard; waits
  on G6.

  Self adversarial pass: quantifiers are finite and explicit; no claim that
  μ alone gives width; the width 1 clause is reconciled by the intermediate
  band. Worst gap: G6 (monotone transform plus swap). No barrier issue at
  resolution level. Status: prose ready for formalize of G5 (definitions and
  intermediate existence); G6 needs its own formalize after G5 merges.

  Next: formalize G5 (L, comp, subadditivity, intermediate clause).
- 2026-08-03 formalize (G5: L, pigeonComplexity, intermediate existence):
  SUCCESS. Extended ClauseComplexity.lean (plus Derivation.conclusion in
  Resolution.lean for term level parent clauses). Certified: Crit.leftOut_eq,
  Crit.leftOut_iff, mem_L_iff, L_empty, pigeonComplexity_empty, L_pigeonClause,
  pigeonComplexity_pigeonClause, L_holeClause, pigeonComplexity_holeClause,
  L_resolvent_subset, pigeonComplexity_resolvent_le, pigeonComplexity_php_hyp_le,
  exists_intermediate_of_high_pigeonComplexity, exists_intermediate_pigeonComplexity
  (n ≥ 1). Gate green. Correction vs prior prose: width 1 positive literal has
  full L = univ only when n ≥ 2 (for n = 1 the unique hole forces placement);
  that corollary was not certified this cycle and is not needed for G5.
  Pending human gate merge_certified. Next after merge: formalize G6 (monotone
  transform and (n+1−m)m width bound).
- 2026-08-03 human gate merge_certified: G5 pigeonComplexity cluster (14
  declarations) accepted into the accepted tree. Gate remains green. R1 stays
  active. Next: formalize G6.
- 2026-08-03 formalize (G6: monotone transform and one-pigeon width): PARTIAL
  SUCCESS. New module MonotoneWidth.lean. Certified: grid decoding; Buss
  monotone transform with critical equivalence (L and pigeonComplexity
  invariant); swap construction; monotoneClause_contains_swap_literal;
  monotoneClause_card_one_pigeon ((n+1)−m ≤ |monotoneClause| for each
  i ∈ L(C)). Gate green. Deferred to next formalize: product assembly
  m·((n+1)−m) over all i ∈ L and the intermediate quadratic 2(n+1)²/9.
  Pending human gate merge_certified for the G6 cluster. Next: formalize
  product width bound.
- 2026-08-03 human gate merge_certified: G6 MonotoneWidth cluster (23
  declarations) accepted into the accepted tree. Gate remains green. R1 stays
  active. Next: formalize product width m·((n+1)−m) and intermediate quadratic.
- 2026-08-03 formalize (G6 product width and intermediate quadratic): SUCCESS.
  Extended MonotoneWidth.lean. Certified: chosenFalsifier; forcedLitsAll with
  pairwise disjointness; forcedLitsAll_card (= m·((n+1)−m));
  monotoneClause_card_ge; intermediate_product_ge ((k/3)² on the band
  k/3 < m ≤ 2k/3); monotoneClause_card_intermediate. Honest Nat bound is
  (k/3)², not the continuum 2k²/9. Gate green (74 accepted decls). Pending
  human gate merge_certified for the product cluster. Next after merge:
  formalize G7 restriction size assembly toward php_resolution_size_lower_bound.
- 2026-08-03 human gate merge_certified: G6 product cluster (8 declarations:
  chosenFalsifier_leftOut, chosenFalsifier_falsifies, forcedLitsAll_subset,
  forcedLitsOne_disjoint, forcedLitsAll_card, monotoneClause_card_ge,
  intermediate_product_ge, monotoneClause_card_intermediate) accepted into
  the accepted tree. Gate remains green. R1 stays active. Next: formalize G7
  restriction size assembly toward php_resolution_size_lower_bound.
- 2026-08-03 formalize (G7: matching restriction and large clause averaging):
  PARTIAL SUCCESS. New module MatchingRestriction.lean. Certified: gridPosLits;
  matchingForced and matchingLookup; restrictClause kill of positive placement;
  double counting exists_popular_grid_literal; large_survivors_le; bridge
  monotoneClause_card_ge_largeThreshold. Honest threshold choice:
  largeThreshold = ((n+1)/3)² (certified G6 width), not paper V/10 which needs
  the stronger 2(n+1)²/9 width. Gate green (87 accepted decls). Deferred:
  derivation transport under matching, iterative shrink, smaller PHP isomorphism,
  close Frontier php_resolution_size_lower_bound. Pending human gate
  merge_certified. Next after merge: formalize G7b derivation restriction.
- 2026-08-03 human gate merge_certified: G7 MatchingRestriction cluster (14
  declarations: mem_gridPosLits_iff, gridPosLits_card,
  largeThreshold_eq_intermediate_sq, mem_matchingForced_place,
  mem_matchingForced_row, mem_matchingForced_col, matchingLookup_place,
  restrictClause_none_of_killed, card_eq_sum_ite_mem, sum_card_eq_sum_hitCount,
  exists_popular_grid_literal, filter_not_killed_card, large_survivors_le,
  monotoneClause_card_ge_largeThreshold) accepted into the accepted tree.
  Gate remains green. R1 stays active. Next: formalize G7b derivation
  restriction under matching.
