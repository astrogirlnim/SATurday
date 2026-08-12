# Proof Complexity Ladder (Record of Rungs)

The single source of truth for what the program is climbing, in what order, and
where each rung stands. One rung memory file per rung in docs/ladder/rungs/.
Statuses: proposed | active | prose_accepted | certified | blocked | killed.

Update discipline: the saturday session is the only writer. Statuses change only
through session actions. Human gates: adopting or killing a rung, accepting a prose
proof for formalization, and merging a certified result into the accepted tree.

## DAG

R0 -> R1 -> R2 -> R3 -> R4 -> summit
R5 (bridge) starts after R1 and joins the summit edge: the final theorem requires
R4-class results plus the certified R5 bridge.

## Rungs

- R0 resolution foundations
  - status: certified (2026-08-03, axiom gate green)
  - statement: resolution soundness and refutational completeness, certified in Lean
  - memory: docs/ladder/rungs/r0-resolution-foundations.md
  - lean: theory/Theory/ProofComplexity/Resolution.lean

- R1 PHP Haken lower bound
  - status: certified (2026-08-04, honest exponential rate; gate green)
  - statement: resolution refutations of PHP(n+1, n) require size exponential in n
  - memory: docs/ladder/rungs/r1-php-haken.md
  - lean: theory/Theory/ProofComplexity/MonotoneCalculus.lean
    (`php_resolution_size_lower_bound`; family defs in PHP.lean)

- R2 width machinery
  - status: prose_accepted (2026-08-04, human gate accept_prose)
  - statement: Ben-Sasson-Wigderson width-size tradeoff, random k-CNF and Tseitin
    expander lower bounds
  - memory: docs/ladder/rungs/r2-width-machinery.md
  - lean: Width.lean and SizeWidth.lean (item 1 BSW merged); FinGraph.lean and
    Tseitin.lean (item 2 Tseitin width machine and Heawood expansion merged);
    CSExpansion.lean (clause-set CS width machine certified; pin restated
    2026-08-09 to IsCSMatchable / HasCSClauseExpansion; matchability
    infrastructure merged 2026-08-10; Spreads reduction to
    HasCSClauseExpansion merged 2026-08-10; finite Spreads r=2 unsat witness
    merged 2026-08-10; informative floor threshold and Spreads scale 3
    constructor merged 2026-08-10; single support starCNF encoding and
    SpreadsSupports scaffolding merged 2026-08-10; cubic handshaking and
    Heawood star Spreads at r = 5 merged 2026-08-10; matching
    SpreadsSupports at informative r = 8 merged 2026-08-11; overlapping
    loose path SpreadsSupports and polarity CNF packaging merged 2026-08-11;
    probabilistic ensemble scaffolding (`Ensemble3CNF` / `random3CNF` /
    packaging) merged 2026-08-11; unsat first-moment Nat bounds
    (`exists_unsat_random3CNF`) merged 2026-08-11; Spreads and matchability
    union-bound scaffolding (`SpreadsIndices`, concentration fibers,
    `isCSMatchable_of_unsat_min_card`) merged 2026-08-11; Spreads summed choose
    packaging and crude close obstruction at n = 32 merged 2026-08-11; prove
    revision 2026-08-11: abandon crude `spreadsFailureTerm` close, switch Step 3
    to occupancy tails at locked `m = 6 n`, `r = n / 4` (pin shrink fallback
    recorded); occupancy packaging Cluster 21 merged 2026-08-11 after human
    accept_prose on that revision (`spreadsOccupancyTerm`,
    `exists_spreadsIndices_of_occupancy_sum_lt`); Frontier
    exists_spreads_matchable_unsat_random3CNF and
    exists_cs_clause_expanding_3cnf still open: Cluster 22 certified that
    Chernoff single slice occupancy already overruns the first moment budget
    at locked `n = 32`, `s = 8`, so the `m = 6 n`, `r = n / 4` union bound
    is blocked; prove 2026-08-11 kills that pin and the recorded `r = n / 8`
    fallback under the same first moment method; Cluster 23 (2026-08-12,
    human accept_prose) activates `random3CNFMatchScale := n / 16` with
    `n ≥ 128`, retargets packaging and Frontier equations; existence still
    Frontier pending Nat Chernoff or occupancy close)

- R3 stronger systems
  - status: proposed
  - statement: one certified lower bound above resolution (Res(k), cutting planes
    via interpolation, or bounded-depth Frege PHP)
  - memory: docs/ladder/rungs/r3-stronger-systems.md

- R4 open frontier
  - status: proposed
  - statement: super-polynomial lower bound for a system with no known bounds,
    first subtarget AC0[p]-Frege
  - memory: docs/ladder/rungs/r4-frontier.md

- R5 Cook-Reckhow bridge
  - status: active (opened by R1 certification; bridge formalization may start)
  - statement: P, NP, coNP, proof systems, and the bridge theorems formalized;
    poly-bounded system exists iff NP = coNP; P = NP implies NP = coNP
  - memory: docs/ladder/rungs/r5-cook-reckhow-bridge.md

## Edge conditions

- R0 -> R1: R0 certified (gate passes) and R1 statement certified in Lean.
- R1 -> R2: R1 certified or R1 prose_accepted with formalization in progress and
  no blocker; R2 may also open early if R1 route chooses the width method.
- R2 -> R3: width machinery certified in general form.
- R3 -> R4: one above-resolution bound certified and its technique documented
  against the R4 walls (docs/p-vs-np-barrier-evasion.md).
- R1 -> R5: R1 certified triggers the bridge formalization start.
- R4 + R5 -> summit: all-systems lower bound program plus certified bridge.
