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

## Known blockers (as of session start)
1. Stalks are sets, not abelian groups. Standard sheaf cohomology requires abelian
   group stalks. The construction must be linearized (e.g., free Z-module or F_2
   coefficients) and the satisfiability correspondence verified to survive.
2. The sheaf lives over 2^n vertices. A polynomial-size chain complex derived from
   the CNF formula (not an explicit enumeration) must be constructed for the
   complexity question to be well-posed.
3. The equivalence "H^1(F) = 0 iff phi is satisfiable" (or an analogous hardness
   correspondence) is a conjecture, not a theorem.
4. Relativization is admitted as unresolved and must be addressed before any claim
   of a P vs NP separation.

## Recommended near-term research path
1. Compute H^1 of random 3-SAT instances near the satisfiability threshold
   numerically for small n (n up to 30 is feasible with existing tools).
2. Determine empirically whether the cohomological transition coincides with the
   satisfiability threshold at ratio approximately 4.267 clauses per variable.
3. Prove or disprove the H^1-satisfiability correspondence for 2-SAT, where
   satisfiability is polynomial and cohomology is well-understood.
4. Formalize the first Lean target (global sections = satisfying assignments)
   as a foundation for future mechanized proofs.

## Status
Active. Session started: 2026-04-12.

## Key references
Mulmuley and Sohoni (2001): background on geometric obstruction methods.
Linial and Meshulam (2006): cohomological thresholds in random complexes.
Babson, Hoffman, Kahle (2011): phase transitions in random topology.
Aaronson and Wigderson (2009): algebraization barrier.
Razborov and Rudich (1997): natural proofs barrier.
Baker, Gill, Solovay (1975): relativization barrier.
