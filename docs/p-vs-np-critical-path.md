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
      Accepted route recorded in file: matchable unsat 3 CNF with
      `Spreads F (n/4) 2`, then `hasCSClauseExpansion_one_of_spreads_two`.
      Progress 2026-08-11: SpreadsSupports matching and overlapping path
      certified; polarity CNFs still satisfiable. Accept_prose approved for
      probabilistic lift. Formalize cycle certified ensemble scaffolding:
      `Ensemble3CNF` / `random3CNF` / packaging
      `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` (axiom gate
      green). Remaining: Frontier counting
      `exists_spreads_matchable_unsat_random3CNF` (Spreads and matchability
      union bounds at `m = 6 n`, `r = n/4`; unsat first-moment
      `exists_unsat_random3CNF` certified 2026-08-11).
- [ ] Quarantined variable side Frontier sorries stay archival; do not spend
      cycles on them unless the pin is restated again.
- [ ] Human gate: move R2 from `prose_accepted` to `certified` only after the
      existence pin is axiom gate green (or redesign the pin and re prove).

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

1. R2: tighten occupancy fibers (Chernoff or relative entropy, not the inner
   `∑_u C(n,u)` union) then close joint unsat and matchability for
   `exists_spreads_matchable_unsat_random3CNF` at density `m = 6 n` and scale
   `r = n/4` (occupancy packaging Cluster 21 merged; edit CSExpansion.lean
   only; fallback pin `r = n/8` recorded but inactive).
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
