# P vs NP Remaining Critical Path

One page checklist from current HEAD (`2776f2a`, 2026-08-11) to a machine
checkable `P != NP` argument under the locked proof complexity attack.
Statuses are taken from `docs/ladder/ladder.md` and rung memories; do not treat
this file as a second ladder. Update only when a saturday cycle changes a listed
item.

## Goal (unchanged)

Super polynomial lower bounds for all propositional proof systems imply
`NP != coNP` (Cook Reckhow), which implies `P != NP`. Summit needs R4 class
hardness plus a fully certified R5 bridge. Neither is complete.

## Done (do not reopen without cause)

- [x] R0 resolution soundness and completeness
- [x] R1 PHP size lower bound (honest exponential rate; paper rate not claimed)
- [x] R2 item 1 Ben Sasson Wigderson size width machine (`SizeWidth.lean`)
- [x] R2 item 2 Tseitin or expander width machine (`FinGraph.lean`, `Tseitin.lean`)
- [x] R2 CS width scaffolding and Spreads or star helpers (`CSExpansion.lean`
      accepted parts)
- [x] R5 Encoding and Complexity classes (`InP`, `InNP`, `InCoNP`)
- [x] R5 Lemma A: `InP_implies_InNP`
- [x] R5 Lemma B: `classP_eq_classNP_implies_NP_eq_coNP` (needs `InP_complement`)

## Critical path (ordered)

### Block A: Finish R2 (blocks R2 certified and clean R3 open)

- [ ] Close Frontier `CSExpansionFrontier.exists_cs_clause_expanding_3cnf`
      (`theory/Theory/ProofComplexity/CSExpansion.lean`).
      Route: matchable unsat 3 CNF with `Spreads F r 2` then
      `hasCSClauseExpansion_one_of_spreads_two`. Ensemble scaffolding and
      packaging `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`
      certified; unsat first moment `exists_unsat_random3CNF` certified.
      Cluster 22 killed first moment Spreads close at locked `m = 6 n`,
      `r = n / 4`. Prove 2026-08-11 killed `r = n / 8`. Cluster 23 activated
      `r = n / 16`, but prove 2026-08-12 kills that first moment plan too:
      full slice `C(m,s) C(n,2s-1) ((2s-1)/n)^{3s}` is about `1.7e15` at
      `n=128`, `r=8`, and rate `α(3+ln 12)>0` for every linear `α`. Do not
      Nat chase Chernoff under Spreads rate 2. Cluster 25 certified
      `ExpandsIndices` lift and Spreads free packaging
      `exists_cs_clause_expanding_3cnf_of_matchable_unsat_expanding`.
      Prove 2026-08-15: unique neighbor first moment is equivalent to Spreads
      rate 2 for 3 CNF (dead at unsat densities); do not Nat chase `α⋆`.
      Revised Block A (accept_prose pending): primary unbounded existence via
      Tseitin on an infinite 3 regular expander family, reusing accepted
      `tseitin_expander_width_lower_bound`; random CS Frontier secondary.
- [ ] Quarantined variable side Frontier sorries stay archival; do not spend
      cycles on them unless the pin is restated again.
- [ ] Move R2 from `prose_accepted` to `certified` only after the existence
      pin is axiom gate green (merge_certified human gate).

### Block B: R3 one bound above resolution (blocks credible R4)

- [ ] Adopt R3 (human gate): choose one of Res(k), cutting planes via
      interpolation, or bounded depth Frege PHP
      (`docs/ladder/rungs/r3-stronger-systems.md`).
- [ ] Prove cycle: pin Lean statement, gaps, falsification test.
- [ ] Formalize to axiom gate green; document technique reuse and walls toward R4.
- [ ] Human gate: R3 `certified`.

### Block C: R4 open frontier (this is the research wall)

- [ ] Adopt R4 subtarget (default order: AC0[p] Frege, then TC0 Frege, Frege,
      extended Frege).
- [ ] Barrier audit and falsification tests T4.1 and T4.2 before deep formalize.
- [ ] Produce a prose argument that survives audit.
- [ ] Formalize a super polynomial lower bound for a system with no known such
      bound.
- [ ] Human gate: R4 `certified`.
- [ ] Repeat or extend until the program covers the systems needed for the
      summit packaging you claim (simulation order: each system is its own wall).

### Block D: Finish R5 bridge (needed for summit link; parallelizable with A to C)

Complexity half is done. Remaining modules from the R5 plan
(`docs/ladder/rungs/r5-cook-reckhow-bridge.md`):

- [ ] `Bridge/FormulaEncoding.lean`: formulas, poly time encode or decode,
      semantic `Tautology`, language `TAUT` (or UNSAT CNF form).
- [ ] `Bridge/ProofSystem.lean`: `IsPropProofSystem`, `PolynomiallyBounded`,
      truth table system nonvacuity witness.
- [ ] Lemma C (Bridge theorem 1, =>): poly bounded proof system implies
      `ClassNP = ClassCoNP`. Hard gap: poly time many one reduction from every
      coNP language to TAUT (or NP to SAT).
- [ ] Lemma D (Bridge theorem 1, <=): `ClassNP = ClassCoNP` implies a poly
      bounded proof system exists.
- [ ] Lemma E (summit corollary): no poly bounded system implies
      `ClassP != ClassNP` (from Lemmas C and B; no lower bound as axiom).
- [ ] `Bridge/CookReckhow.lean` packaging; root import when gate ready.
- [ ] Human gate: R5 `certified` only when 9 to 11 in the R5 pin are accepted.

### Block E: Summit packaging

- [ ] Compose: R4 class “no poly bounded system” evidence with certified Lemma E.
- [ ] Checklist sections 6 and 7 (`docs/p-vs-np-solve-checklist.md`): full
      implication chain, trusted core, reproducibility, red team.
- [ ] Freeze and publish machine checkable package.

## What not to do on the critical path

- More R5 Complexity polish (composition generality, mathlib `comp`) unless a
  later lemma needs it.
- R2 quarantined variable side Frontier theorems.
- Reopening R0 or R1 for rate cosmetics.
- Treating Lemma A or B alone as progress toward `P != NP`.

## Suggested saturday priority when you resume

1. R2: human gate accept_prose on prove 2026-08-15 (kill unique neighbor first
   moment; pivot Block A to unbounded Tseitin expanders). After gate:
   formalize or construct an infinite 3 regular `HasExpansion` family and
   package size or width lower bounds via existing Tseitin lemmas. Do not
   Nat chase Spreads or `ExpandsIndices` first moment.
2. In parallel sessions only: R5 FormulaEncoding start (definitional; no summit
   claim until Lemmas C to E).
3. Do not open R3 until R2 is certified or explicitly blocked with a kill or
   redesign decision.

## Live pointers

- Ladder: `docs/ladder/ladder.md`
- R2 memory: `docs/ladder/rungs/r2-width-machinery.md`
- R5 memory: `docs/ladder/rungs/r5-cook-reckhow-bridge.md`
- Attack lock: `docs/p-vs-np-main-attack.md`
- Lemma chain: `docs/p-vs-np-lemma-chain.md`
- Working checklist: `docs/p-vs-np-solve-checklist.md`
