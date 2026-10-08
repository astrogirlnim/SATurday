# R4 Research and Certification Plan

Status of R4: proposed (no adopt decision yet). Written 2026-10-07 after R3 was certified.

## What R4 asks

A super polynomial lower bound for a propositional proof system with no known super
polynomial lower bound. Default first subtarget: AC0[p] Frege (bounded depth Frege with
mod p counting connectives), open since the late 1980s. TC0 Frege, Frege and extended
Frege follow, each its own wall. The summit needs the all systems statement, which is
equivalent to NP ≠ coNP. That is P vs NP class difficulty, not a formalization task.

## Why the loop alone cannot do it

- The loop formalizes and audits arguments; it does not create new mathematics. R0 to R3
  were known theorems; R4 has no known proof.
- Local 14B models could not design the R3 constructions (Pudlák interpolation, the
  approximation method). R4 needs ideas beyond any published technique.
- R3 techniques stop here: interpolation fails for TC0 Frege under standard hardness
  assumptions, and approximation methods have not reached AC0[p] Frege.

The loop is still useful for: bookkeeping, falsification runs, barrier audits, and
filling micro lemmas once a human or strong model has fixed exact Lean statements.

## Plan

### Phase 0: lock the target (human gate)

- [ ] Adopt R4 with an exact Lean statement: a family `F_n` (candidates: Tseitin mod q on
  expanders, Count_q, onto PHP, random k CNF), a system (AC0[p] Frege of depth `d`), and a
  super polynomial bound. Record a non vacuity witness (`F_n` unsatisfiable).
- [ ] Record kill conditions: a quasi polynomial upper bound kills the family (T4.1). An
  argument that would also prove a known false or crypto breaking statement fails the
  barrier audit (T4.2).

### Phase 1: certified infrastructure (feasible, months)

Known mathematics that any attack will reuse; each item is a certifiable milestone.

- [ ] Lean definitions: Frege, depth `d` Frege, AC0[p] Frege (mod p gates), size and depth,
  soundness.
- [ ] Razborov–Smolensky: AC0[p] circuits cannot compute MOD_q (polynomial approximation
  over F_p). This is the circuit analogue of R4.
- [ ] Håstad switching lemma and the bounded depth Frege lower bound for PHP (Ajtai;
  Pitassi–Beame–Impagliazzo; Krajíček–Pudlák–Woods). This is the closest known proof result.
- [ ] Polynomial calculus degree lower bounds over F_p (Razborov; Alekhnovich–Razborov
  for Tseitin mod q), plus size–degree tradeoffs.
- [ ] Known partial results toward AC0[p] Frege: Count_q lower bounds for bounded depth
  Frege with Count_p axioms (Beame–Riis; Buss–Impagliazzo–Krajíček–Pudlák–Razborov–Sgall);
  Res(⊕) and regular Res(⊕) lower bounds (2023–2024 literature, to be confirmed in a
  literature pass).

### Phase 2: intermediate open targets (research, measurable)

Climb toward AC0[p] Frege through strictly stronger systems with open or recent bounds:

- [ ] Res(⊕) (resolution over parities) in full generality, then Res(lin F_p).
- [ ] Depth 2, then constant depth, AC0[p] Frege for small depth.
- [ ] Each step: prose proof, barrier audit, adversarial counterexample attempts (stop
  conditions: 3 failures kill the branch), then formalization.

Candidate methods to evaluate (none known to work at the R4 level): lifting PC degree
bounds through restrictions; proof versions of polynomial approximation; random
restriction and switching arguments adapted to mod p gates; algebraic or
semantic interpolation variants that avoid known barriers.

### Phase 3: certify (only after a prose proof survives audit)

- [ ] Formalize in Lean in micro lemmas (the loop fills small lemmas; a human or strong
  model fixes statements and constructions).
- [ ] Axiom gate PASS locally and in CI; declarations listed in
  `scripts/accepted_declarations.txt`.
- [ ] Independent review: external expert reading of the prose and the Lean statement
  (statement fidelity is the main risk, not the proof checker).
- [ ] Human gate: R4 `certified`.

## Roles

- Operator: adopt gate, route choices, external review contacts.
- Strong model or mathematician: constructions, prose proofs, exact Lean statements.
- Local loop: falsification, audits, micro lemma formalization, bookkeeping.

## Honest expectation

Phase 1 is achievable and worth doing. Phase 2 contains open problems, and success there
would be publishable research. Completing R4 as stated would resolve a decades old open
problem. No timeline can be promised.
