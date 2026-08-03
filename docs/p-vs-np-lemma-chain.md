# P vs NP Core Lemma Chain (Proof Complexity Ladder)

Primary framework: proof complexity ladder (see docs/p-vs-np-main-attack.md).

Final theorem target:

- P != NP, reached via: super-polynomial lower bounds for all propositional proof
  systems imply NP != coNP (Cook-Reckhow), which implies P != NP.

Ladder rungs (critical path). Each rung is one crisp falsifiable statement.
Live status and per-rung memory: docs/ladder/ladder.md and docs/ladder/rungs/.

1. **R0 (known; pipeline shakedown)**
   Resolution formalized in Lean: literals, clauses, CNF, size-counted resolution
   derivations, soundness (a refutable CNF is unsatisfiable) and refutational
   completeness (an unsatisfiable CNF has a resolution refutation).
   Lean home: theory/Theory/ProofComplexity/Resolution.lean.

2. **R1 (adaptation; first certified lower bound)**
   Haken 1985: the pigeonhole family PHP with n+1 pigeons and n holes requires
   resolution refutations of size exponential in n. Candidate routes: Haken
   bottleneck counting, or the Ben-Sasson-Wigderson width method (R2 machinery
   pulled forward). Lean home: theory/Theory/ProofComplexity/PHP.lean.

3. **R2 (adaptation; general machinery)**
   Ben-Sasson-Wigderson width-size tradeoff formalized in general form, plus
   resolution lower bounds for random k-CNF (Chvatal-Szemeredi) and Tseitin
   formulas over expanders.

4. **R3 (adaptation; stronger systems with known bounds)**
   One of: Res(k) lower bounds, cutting planes lower bounds via feasible
   interpolation (Pudlak), or bounded-depth Frege lower bounds for PHP
   (Ajtai; Pitassi-Beame-Impagliazzo; Krajicek-Pudlak-Woods). Selection is made
   by prover cycles based on formalization cost and technique reuse toward R4.

5. **R4 (new; the open frontier)**
   Super-polynomial lower bounds for systems where none are known. Ordered
   subtargets:
   - AC0[p]-Frege (bounded-depth Frege with counting gates): open since the late
     1980s despite the circuit analogue (Razborov-Smolensky) being known.
   - TC0-Frege, then full Frege, then extended Frege.
   Candidate hard families: counting principles Count(q) against mod q' reasoning,
   Tseitin contradictions over expanders, proof complexity generators.
   This is where prose-proof search concentrates; every candidate argument gets a
   barrier audit and an immediate falsification test before deep expansion.

6. **R5 (adaptation, deferred; the formal bridge)**
   Cook-Reckhow in Lean: define P and NP over a real machine model (mathlib
   Turing.TM2ComputableInPolyTime as the base), define propositional proof systems
   as polynomial-time verifiable onto maps for TAUT (or UNSAT), prove that a
   polynomially bounded system exists iff NP = coNP, and that P = NP implies
   NP = coNP. Deferred until R1 is certified; until then the bridge is informal and
   is never encoded as an axiom.

Lemma classification table:

- R0: known (textbook; formalization cost only).
- R1: adaptation (known theorem, real formalization milestone).
- R2: adaptation (known machinery, generalization work).
- R3: adaptation (known theorems, heavy formalization).
- R4: new (open mathematics; the actual research frontier).
- R5: adaptation (known theorem, heavy computability formalization).

Immediate falsification tests:

- R1 T1.1: run the falsifier on PHP instances; if a resolution proof of size
  polynomial in n is found empirically for growing n (proof sizes fit a polynomial
  curve), the statement of R1 is wrong and the formalization target is corrected
  before further work. (Expected: sizes grow exponentially, consistent with Haken.)
- R4 T4.1: for each candidate hard family and target system, search the literature
  and run bounded empirical proof search for short proofs in simulable fragments;
  quasi-polynomial upper bounds kill the family for that rung.
- R4 T4.2: every proposed lower-bound argument must name the property of the proof
  system it exploits and pass the barrier audit (docs/p-vs-np-barrier-evasion.md)
  before formalization effort is spent.

Lean-precision filter (must pass before a rung stays on the critical path):

- R0: pass (finite syntactic objects).
- R1: pass (explicit CNF family, size-counted derivations, explicit bound).
- R2: pass (explicit width and size measures).
- R3: pass (explicit proof systems; interpolation statements are finite).
- R4: pass for statement shape (same objects as R3); proof content open.
- R5: pass (mathlib computability primitives exist; poly-time bounds statable).

Non-vacuity rule (from the Bet A postmortem): every lower-bound rung must include a
positive witness that the target family has proofs in the system at all (soundness
side: the family is genuinely unsatisfiable; system side: completeness guarantees
refutations exist, so lower bounds quantify over a nonempty set).
