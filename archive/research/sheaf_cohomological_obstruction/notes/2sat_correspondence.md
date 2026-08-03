# 2-SAT Correspondence: H^1(F; F_2) vs Satisfiability

## Goal

Prove or disprove: for the solution-space sheaf F over partial assignments of a
2-SAT formula, H^1(F; F_2) = 0 if and only if the formula is satisfiable.

If this fails for 2-SAT, the entire sheaf-cohomological approach is wrong before
any Lean formalization begins. 2-SAT is the cheapest possible sanity check: it is
polynomial-time solvable, its solution space has clean structure, and cohomology
over F_2 is well-understood.

---

## Setup

Let phi be a 2-CNF formula on variables x_1, ..., x_n. Each clause has exactly
two literals.

### The solution-space sheaf F

Base space: the poset P of partial assignments, ordered by extension.
- A partial assignment sigma is a function sigma: S -> {0, 1} for some S subset {1,...,n}.
- The empty assignment is the bottom element.
- The total assignments (S = {1,...,n}) are maximal elements.

Stalk F(sigma): the set of satisfying total assignments that extend sigma.
Formally:
  F(sigma) = { tau in {0,1}^n : tau extends sigma and tau satisfies phi }

Restriction map rho_{sigma <= tau}: F(sigma) -> F(tau)
  For sigma <= tau (tau extends sigma), the map sends a satisfying total assignment
  alpha in F(sigma) to alpha itself, viewed as an element of F(tau).
  In other words: rho(alpha) = alpha if alpha extends tau, else undefined.

This makes F a presheaf of sets on P.

### Linearization to F_2-coefficients

To apply cohomology we must replace set-valued stalks with F_2-vector spaces.

Define the linearized sheaf F_lin:
  F_lin(sigma) = (F_2)^{F(sigma)} = the free F_2-vector space on the set F(sigma).

The restriction map rho_{sigma <= tau} extends linearly:
  rho_lin(e_alpha) = e_alpha if alpha in F(tau), else 0.

Global sections of F_lin:
  H^0(F_lin) = lim_{<-} F_lin = { (v_sigma) : for all sigma <= tau, rho_lin(v_sigma) = v_tau }.

A global section is a consistent choice of element of F_lin(sigma) at every
partial assignment, compatible under restriction.

---

## H^0 = satisfying assignments (the easy direction)

Claim: H^0(F_lin) is isomorphic (as an F_2-vector space) to (F_2)^{Sol(phi)},
where Sol(phi) is the set of satisfying total assignments.

Proof:
Each satisfying total assignment alpha determines a global section: set v_sigma = e_alpha
for every sigma that alpha extends, and v_sigma = 0 for every sigma that alpha does not
extend. This is consistent under restriction maps by definition.

Conversely, any global section must be supported on satisfying assignments at the maximal
(total assignment) stalks, and the consistency conditions propagate this back to all
partial assignments.

Therefore H^0(F_lin) = (F_2)^{Sol(phi)}, so dim H^0 = |Sol(phi)|.

In particular: phi is satisfiable iff dim H^0 >= 1. This direction is sound and survives
linearization. It is the formal target for the first Lean theorem.

---

## H^1 for 2-SAT: analysis

We need to understand whether H^1(F_lin) = 0 for satisfiable 2-SAT instances, and
H^1(F_lin) != 0 for unsatisfiable ones.

### Cech cohomology on a poset

The Cech complex for a sheaf on a poset P is:
  C^0 = prod_{sigma} F(sigma)
  C^1 = prod_{sigma <= tau} F(sigma)   [one factor per cover relation]
  C^p = prod_{sigma_0 < sigma_1 < ... < sigma_p} F(sigma_0)

with coboundary maps d^p: C^p -> C^{p+1} defined by the alternating sum of
restriction maps.

H^1 = ker(d^1) / im(d^0).

### The poset structure for 2-SAT

For n variables, the poset of partial assignments has:
  - 1 bottom element (empty assignment)
  - n elements at depth 1 (single-variable assignments)
  - n(n-1)/2 * 4 ... elements at deeper levels
  - 2^n maximal elements (total assignments)

The sheaf F_lin has stalks of size at most 2^n at the bottom. Most importantly:
- At the empty assignment: F_lin(empty) = (F_2)^{Sol(phi)} -- dimension = |Sol(phi)|
- At a total assignment alpha: F_lin(alpha) = F_2 if alpha satisfies phi, else {0}

### Key structural observation for 2-SAT

For 2-SAT, the solution space Sol(phi) has a very particular structure. Via the
implication graph, 2-SAT is satisfiable iff no variable and its negation are in
the same strongly connected component (SCC).

When 2-SAT is satisfiable, Sol(phi) is non-empty but can be exponentially large.
The restriction maps between stalks of F_lin are surjective in the satisfiable case:
for any partial assignment sigma that is consistent with phi (i.e., can be extended
to a satisfying assignment), the restriction from F_lin(empty) to F_lin(sigma) is
surjective onto the basis elements that survive.

When 2-SAT is unsatisfiable, F_lin(alpha) = 0 for every total assignment, so all
stalks are zero and H^1 = 0 trivially.

CRITICAL OBSERVATION: If phi is UNSATISFIABLE, then Sol(phi) = empty, so F_lin(sigma) = 0
for all sigma. A sheaf with all-zero stalks has H^p = 0 for ALL p. In particular H^1 = 0.

So H^1 = 0 for UNSATISFIABLE instances. The conjecture "H^1 = 0 iff satisfiable" would
require H^1 != 0 for satisfiable instances, which is the WRONG direction from what
one might naively expect.

### Revised conjecture

The correct direction for the obstruction should be:
  phi is UNSATISFIABLE iff some cohomological invariant is NONZERO.

For H^0 this works: H^0 = 0 iff phi is unsatisfiable.

For H^1: the analysis above shows that H^1 = 0 for all unsatisfiable instances (trivially,
since all stalks are zero). For satisfiable instances, H^1 may or may not be zero.

This means H^1 of the solution-space sheaf CANNOT serve as an unsatisfiability certificate.
It is the wrong cohomological degree.

---

## Is there a correct cohomological degree?

For a sheaf with stalks that are zero on the unsatisfiable instances, the interesting
invariant must come from a DERIVED or RELATIVE construction, not the absolute H^1.

Possibilities:
(a) Work with the COMPLEMENT sheaf: define G(sigma) = all partial assignments extending
    sigma that CANNOT be extended to a satisfying total assignment. Then H^0(G) = 0 iff
    phi is satisfiable.

(b) Work with a RELATIVE cohomology: compare F_lin to a "trivial" or "clause-free" sheaf
    and take the relative H^1. The relative obstruction measures how clauses block extensions.

(c) Work with a DIFFERENT base space: instead of the poset of partial assignments, use the
    nerve of the cover defined by clauses. This is closer to the original literal clause
    complex idea but with the correct stalks.

(d) Work with HIGHER derived functors of the global section functor. For a sheaf on a
    finite poset, these can be computed combinatorially.

---

## Conclusion

H^1 of the solution-space sheaf does NOT capture satisfiability in the way the original
conjecture stated. Specifically:
  - Unsatisfiable instances: H^1 = 0 (all stalks zero, trivial)
  - Satisfiable instances: H^1 may be zero or nonzero depending on instance

The H^0 identification (dim H^0 = |Sol(phi)|) IS correct and survives linearization.
This is a sound theorem worth formalizing in Lean 4.

The hardness claim must be reformulated. The correct cohomological object is likely
a derived functor or relative cohomology, not H^1 of the direct solution-space sheaf.

### Immediate implications for the research program

1. The first Lean target (H^0 = satisfying assignments) is still valid and worth formalizing.
   It establishes the foundation: the sheaf exists, linearizes correctly, and global
   sections capture exactly what we want.

2. The H^1 conjecture needs reformulation before any Lean work on obstruction theory.
   The two most tractable reformulations are (b) and (c) above.

3. For 2-SAT specifically: the tractable path is to prove that the RELATIVE H^1
   (relative to the clause cover) equals zero iff 2-SAT is satisfiable. This can be
   verified against the implication-graph algorithm.

4. The relativization concern from the README (corner case: a sheaf defined over a
   computation tree might relativize) is STILL UNRESOLVED and must be addressed before
   any separation claim.

### Next step

Write notes/linearization.md to commit to F_2 coefficients formally and define
restriction maps precisely. Then determine which of (b), (c), (d) above is the
correct obstruction object for the 2-SAT test case.

---

## Status: PRELIMINARY ANALYSIS COMPLETE

H^0 theorem: PROVABLE (first Lean target, sound)
H^1 obstruction conjecture as originally stated: INCORRECT for solution-space sheaf
Revised target: relative cohomology or different base space construction
