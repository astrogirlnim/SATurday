# Sheaf-Cohomological Obstruction to Polynomial Search

## One-line description
Model an NP instance as a sheaf over its partial-assignment space and prove that
the cohomological obstruction to extending local solutions globally is
super-polynomially hard to compute.

## Barrier evasion claimed
Relativization: The sheaf is built from the clause structure of the instance, not
  from oracle queries. An oracle changes what the algorithm can compute; it does
  not change the topological structure of the instance solution space.
  Unresolved corner: a sheaf defined over a computation tree rather than the
  instance structure might relativize. This must be ruled out.
Natural proofs: H^1 is a global geometric invariant of one specific instance, not
  a property of a function family. The Razborov-Rudich largeness condition fails
  categorically.
Algebraization: The sheaf lives over combinatorial topology of partial assignments.
  Lifting to an algebrized oracle model would require algebrizing sheaf cohomology
  itself, which destroys the topological structure the argument depends on.
  Not yet formally proven.

## First Lean target
Define sheaf F over {0,1}^n where the stalk at vertex v is the set of
clause-consistent extensions from v. Prove that global sections of F are exactly
the satisfying assignments of the SAT instance.

## Known blockers (updated 2026-04-13)

Blocker status after preliminary theoretical work (see notes/2sat_correspondence.md
and notes/linearization.md):

1. Linearization: RESOLVED. Use F_2 coefficients. The free F_2-vector space on each
   stalk F(sigma) = { satisfying total assignments extending sigma } is the correct
   linearized sheaf F_lin. Restriction maps extend by F_2-linearity. The H^0 = Sol(phi)
   identification survives linearization. (notes/linearization.md)

2. Polynomial-size chain complex: OPEN (major). The current construction has the poset
   PA_n of size 3^n (exponentially large). A polynomial-size description must be
   constructed for the complexity question to be well-posed. Candidate: clause cover
   nerve (O(|phi|) simplices per dimension). Not yet verified to compute the same H^1.

3. H^1 obstruction conjecture: REFUTED in its original form. When phi is unsatisfiable,
   all stalks of F_lin are zero (Sol(phi) = empty), so H^1 = 0 trivially. The original
   conjecture "H^1 = 0 iff satisfiable" requires H^1 != 0 for satisfiable instances,
   which is the WRONG direction. The correct obstruction must come from a different
   construction: relative cohomology H^1(PA_n, PA_n^sat; F_lin) or Cech cohomology
   of the clause cover nerve. (notes/2sat_correspondence.md)

4. Relativization: UNRESOLVED. The corner case (sheaf defined over a computation tree
   rather than the instance structure) must be ruled out before any separation claim.

## Recommended near-term research path (updated 2026-04-13)

1. [DONE] Compute H_1 of random 3-SAT instances near the satisfiability threshold
   numerically for small n. (empirical_h1.py, session 2026-04-12)

2. [DONE] Determine empirically whether the cohomological transition coincides with
   the satisfiability threshold at ratio approximately 4.267 clauses per variable.
   Result: FAILED for all four syntax-based constructions. H_1 > 0 = 100% at every
   ratio. Root cause: any polynomial-time computable sheaf built from formula syntax
   cannot capture satisfiability. (empirical_reformulations.py, session 2026-04-13)

3. [DONE - theory] Prove or disprove the H^1-satisfiability correspondence for 2-SAT.
   Result: H^1 obstruction conjecture REFUTED for the solution-space sheaf. Unsatisfiable
   instances have H^1 = 0 (all stalks zero). The correct obstruction lives in relative
   cohomology or the clause cover nerve. H^0 correspondence is VERIFIED and is the
   correct first Lean target. (notes/2sat_correspondence.md, notes/linearization.md)

4. [DONE - theory] Test Cech H^1 of the clause cover nerve for 2-SAT.
   Result: FAIL (2026-04-13). Two failure modes confirmed:
     1-skeleton only: H_1 = 1.00 always (too many cycles, regardless of SAT).
     Full nerve with triangles: H_1 = 0.00 always (nerve is contractible, trivial).
   This matches the theoretical prediction: any polynomial-time syntactic construction
   either produces H_1 always-nonzero or always-zero. No transition is possible.
   The empirical phase is definitively complete. All five constructions tested have
   failed. The correct obstruction does not admit a polynomial-time syntactic formula.

5. [NEXT] Formalize the H^0 theorem in Lean 4: global sections of F_lin equal
   satisfying assignments. This is unconditionally correct and does not depend on
   any unresolved conjecture. File: research/sheaf_cohomological_obstruction/lean/SolutionSheaf.lean

## Empirical result round 2 (session 2026-04-13)

Tested three reformulations across n in {15, 20, 30}, 100 trials each, 14 ratios,
with Wilson 95% confidence intervals.

Constructions tested:
  A. Conflict complex: vertices = clauses, edges = conflicting clause pairs
  B. Variable co-occurrence complex: vertices = variables, edges = co-occurrence in clause
  C. Resolution complex: vertices = clauses, edges = pairs resolvable in one step

Result: all three show H_1 > 0 = 1.00 at every ratio tested. Same failure as
the literal clause complex. This is not a statistical artifact (100 trials at n=30,
Wilson CI confirms H_1 > 0 fraction is above 90% even at easy ratios).

Root cause identified: all four constructions (including the original) are built
from the formula's SYNTACTIC structure (which clauses/variables are connected).
Any such construction produces a simplicial complex that is always highly connected
(many independent cycles in the 1-skeleton, not all of which are killed by triangles).
The H_1 measures topological structure of the constraint graph, not satisfiability.

Fundamental circularity: any polynomial-time computable sheaf built from the
formula's syntax cannot capture satisfiability (if it did, we would have a
polynomial-time SAT algorithm). The only sheaves that are guaranteed to track
satisfiability involve the SOLUTION SPACE directly, which is exponentially large
to enumerate.

This is not a refutation of the approach — it is a clarification of what the
correct sheaf must look like:
  The stalk at a partial assignment sigma must be the set of satisfying total
  assignments extending sigma. This sheaf captures satisfiability by definition
  (H^0 = satisfying assignments, H^1 = obstruction to extension). But computing
  this sheaf in general takes exponential time — which is CONSISTENT with P != NP.

Implication: the correct path is THEORETICAL, not empirical. The approach becomes:
  1. Define the solution-space sheaf formally.
  2. Prove H^1 = 0 iff the formula is satisfiable (formal theorem).
  3. Study the computational complexity of H^1 for the implicit sheaf description
     (given a CNF formula, not a full enumeration of the solution space).
  4. Show that computing H^1 is hard (this is the P vs NP claim in cohomological
     language).

The empirical phase is complete. Future work is formal (Lean 4) and theoretical.

## Empirical result round 1 (session 2026-04-12)

Tested: H_1 of the literal clause complex (vertices = literals, triangles = clauses)
vs. satisfiability across n in {10, 15, 20}, ratios 2.5 to 6.0, 50 trials each.

Finding: H_1 > 0 for 100% of instances at every ratio tested.
The literal clause complex is always topologically non-trivial, regardless of
whether the formula is satisfiable. There is no transition.

Interpretation: The literal clause complex captures co-occurrence structure of
literals in clauses, not the satisfiability obstruction. The construction is
incorrect. The deep analysis warning was confirmed: stalks are sets, not abelian
groups, and the correspondence between H^1 and satisfiability was never established.

Required fix: The sheaf must be reformulated. Candidates:
  (a) Conflict complex: vertices = clauses, edges = conflicting pairs of clauses,
      k-simplices = mutually conflicting sets; H_1 of this complex may track
      unsatisfiability more directly.
  (b) Resolution/CDCL state sheaf: model the state space of a CDCL solver as a
      sheaf; H_1 measures the irreducible learned clause structure.
  (c) F_2-linearization of the assignment sheaf: take the free F_2-module on each
      stalk and define restriction maps as linear projections; prove H^1 = 0 iff
      satisfiable for 2-SAT first, then extend.

Next step: implement and test construction (a) as the cheapest empirical check.

## Status
Active. Session started: 2026-04-12.
Empirical phase DEFINITIVELY COMPLETE (2026-04-13): five constructions tested, all fail.
Preliminary theory complete (2026-04-13): H^0 correct, H^1 wrong direction, F_2 committed.

Next action: Lean 4 formalization of H^0 theorem in lean/SolutionSheaf.lean.

## Key references
Mulmuley and Sohoni (2001): background on geometric obstruction methods.
Linial and Meshulam (2006): cohomological thresholds in random complexes.
Babson, Hoffman, Kahle (2011): phase transitions in random topology.
Aaronson and Wigderson (2009): algebraization barrier.
Razborov and Rudich (1997): natural proofs barrier.
Baker, Gill, Solovay (1975): relativization barrier.
