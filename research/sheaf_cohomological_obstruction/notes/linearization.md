# Linearization: Coefficient Ring and Restriction Map Definitions

## Decision: F_2 coefficients

We work over F_2 = {0, 1} (the field with two elements) throughout.

Rationale:
- 2-SAT and 3-SAT are Boolean problems; F_2 is the natural coefficient ring.
- F_2 cohomology avoids sign issues in chain maps.
- Gaussian elimination over F_2 is computationally efficient (relevant for empirical checks).
- The empirical scripts (empirical_h1.py, empirical_reformulations.py) already use F_2.
- Mathlib4 has GF(2) and finite-dimensional vector spaces over finite fields.

Alternative Z-coefficients: would require universal coefficient theorem to relate
to F_2; adds complexity without clear benefit at this stage. Deferred.

---

## Definitions

### 1. Partial assignments

Let n >= 1. A partial assignment on [n] = {1, ..., n} is a pair (S, f) where
S is a subset of [n] and f: S -> {0, 1}.

We write sigma = (S_sigma, f_sigma). The domain of sigma is dom(sigma) = S_sigma.

Extension order: sigma <= tau iff dom(sigma) subset dom(tau) and f_tau restricts
to f_sigma on dom(sigma). Equivalently, tau extends sigma.

The poset (PA_n, <=) has:
  - Unique minimum: the empty assignment bot = ({}, empty_function).
  - Maximal elements: total assignments, i.e., those with dom(sigma) = [n].
  - |PA_n| = sum_{k=0}^{n} C(n,k) * 2^k = 3^n (each variable is 0, 1, or unset).

### 2. Consistency with a formula

Let phi be a CNF formula on variables x_1, ..., x_n.

A partial assignment sigma is consistent with phi (written sigma |= phi partially, or
sigma in Cons(phi)) iff for every clause C of phi, C is not falsified by sigma. A
clause C is falsified by sigma iff every literal of C has its variable in dom(sigma)
and is set to the wrong polarity.

A total assignment tau satisfies phi (written tau |= phi) iff every clause is satisfied.

Sol(phi) = { tau in {0,1}^n : tau |= phi }.

### 3. The solution-space sheaf F

Defined on the poset (PA_n, <=) as follows:

Stalk:
  F(sigma) = { tau in Sol(phi) : tau extends sigma }

For sigma not in Cons(phi): F(sigma) = empty (zero stalk).
For sigma in Cons(phi): F(sigma) may be empty (if sigma cannot be extended to a solution)
  or non-empty.

Restriction map: for sigma <= tau,
  rho_{sigma, tau}: F(sigma) -> F(tau)
  rho_{sigma, tau}(alpha) = alpha   (identity on the underlying total assignment)

This is well-defined: if alpha extends sigma and alpha satisfies phi, and tau extends
sigma with tau <= alpha (i.e., alpha extends tau), then alpha in F(tau).

Note: rho_{sigma, tau} is the identity function on the set F(sigma) intersected with F(tau),
so it is literally a set inclusion F(tau) subset F(sigma) (since tau is more constrained).

Sheaf condition: the gluing axiom holds vacuously at the set level because satisfying
total assignments are the only global sections and they are uniquely determined.

### 4. Linearization

Define the linearized sheaf F_lin over F_2:

Linearized stalk:
  F_lin(sigma) = (F_2)^{F(sigma)}  [free F_2-vector space on the set F(sigma)]

If F(sigma) = empty: F_lin(sigma) = {0} (the zero vector space).
If F(sigma) = {alpha_1, ..., alpha_k}: F_lin(sigma) has basis {e_{alpha_1}, ..., e_{alpha_k}}.

Linearized restriction map:
  rho_lin_{sigma, tau}: F_lin(sigma) -> F_lin(tau)
  rho_lin_{sigma, tau}(e_alpha) = e_alpha  if alpha in F(tau)  (i.e., alpha extends tau)
                                = 0        otherwise

Extend by F_2-linearity. This is well-defined: if alpha in F(sigma), then either
alpha in F(tau) (alpha extends tau, which extends sigma) or alpha does not extend tau.

### 5. The chain complex

For the poset (PA_n, <=), the Cech cochain complex is:

C^p(F_lin) = direct product over all chains sigma_0 < sigma_1 < ... < sigma_p of
  F_lin(sigma_0)

(Convention: sigma_0 is the "bottom" of the chain, with the largest stalk.)

The coboundary d^p: C^p -> C^{p+1} is:
  (d^p s)_{sigma_0 < ... < sigma_{p+1}} = sum_{i=0}^{p+1} (-1)^i * rho_{sigma_0, sigma_i}(s_{sigma_0 < ... < hat{sigma_i} < ... < sigma_{p+1}})

Over F_2, all signs are +1 (since -1 = 1 in F_2).

---

## Correctness verification: H^0 = satisfying assignments

H^0(F_lin) = ker(d^0) = { (v_sigma)_{sigma in PA_n} in C^0 : d^0(v) = 0 }

d^0(v) = 0 means: for every cover relation sigma < tau (i.e., tau = sigma extended by one
variable assignment), rho_lin_{sigma, tau}(v_sigma) = v_tau.

This says: v is a compatible family of vectors, one in each stalk, compatible under
restriction maps.

Claim: H^0(F_lin) is isomorphic to (F_2)^{Sol(phi)}.

Proof sketch:
  Given alpha in Sol(phi), define the global section s_alpha: for each sigma in PA_n,
  let (s_alpha)_sigma = e_alpha if alpha extends sigma, else 0.

  Compatibility: if sigma < tau and alpha extends sigma, then either alpha extends tau
  (so rho_lin(e_alpha) = e_alpha = (s_alpha)_tau) or alpha does not extend tau (so
  rho_lin(e_alpha) = 0 = (s_alpha)_tau, since alpha not in F(tau)).

  Thus {s_alpha : alpha in Sol(phi)} are linearly independent global sections (they have
  disjoint support at the total assignment stalks).

  Conversely, any global section v has v_alpha in F_lin(alpha) = F_2 * {e_alpha} or {0}
  for each total assignment alpha. The compatibility condition forces v to be a sum
  of sections of the form s_alpha.

Therefore dim H^0 = |Sol(phi)|, and H^0 = 0 iff phi is unsatisfiable.

This identification is VERIFIED. It survives linearization. It is the correct first
Lean target.

---

## What goes wrong with H^1

See notes/2sat_correspondence.md for the full analysis. Summary:

When phi is unsatisfiable: F_lin(sigma) = {0} for all sigma (Sol(phi) = empty, so all
stalks are zero). Therefore C^p = 0 for all p, and H^p = 0 for all p >= 0.

In particular H^1 = 0 for all unsatisfiable instances.

The H^1 obstruction hypothesis was WRONG: unsatisfiable instances have H^1 = 0,
not nonzero.

The correct cohomological invariant for detecting unsatisfiability must come from
a different construction. Two candidates:

Candidate (b): Relative cohomology H^1(PA_n, PA_n^{sat}; F_lin), where PA_n^{sat}
is the subposet of partial assignments that are consistent with phi. The relative
cohomology measures how inconsistent partial assignments obstruct extensions.

Candidate (c): Replace the base poset with the nerve of the clause cover.
Each clause C_i defines an open set U_i = { sigma : sigma is consistent with C_i }.
The formula is satisfiable iff the intersection of all U_i is non-empty in a suitable
sense. Cech cohomology of this nerve cover may capture the obstruction.

Both candidates require significant additional development. Neither has been verified
to be sound for the complexity purpose (showing H^1 computation is NP-hard or harder).

---

## Polynomial-size chain complex

The current construction has PA_n of size 3^n. This is exponentially large. For the
complexity question (showing H^1 is hard to compute) to be well-posed, we need a
description of F_lin that is polynomial in n and |phi|.

Candidate polynomial descriptions:
- The chain complex of the clause cover nerve: the nerve has at most |phi| simplices
  per dimension if we use clause as open sets, giving a polynomial-size complex.
- The dual description via implication graph (for 2-SAT): the implication graph has
  O(n + m) edges, giving a polynomial-size starting point.

This is a MAJOR open problem in this approach: constructing a polynomial-size chain
complex that computes the same H^1 as the exponential-size solution-space sheaf.

---

## Summary of what is established

| Claim | Status | Notes |
|---|---|---|
| H^0(F_lin) = Sol(phi) | VERIFIED | First Lean target, sound |
| H^1 = 0 for UNSAT instances | VERIFIED | All stalks zero, trivially |
| H^1 != 0 for SAT instances | UNKNOWN | No evidence either way |
| H^1 = 0 iff SAT | REFUTED | Wrong direction for obstruction |
| Polynomial-size chain complex exists | OPEN | Major blocker |
| Relativization evaded | UNRESOLVED | Corner case not ruled out |

---

## Next steps

1. First Lean target (immediately actionable):
   Define PartialAssignment, solution-space sheaf stalks, restriction maps in Lean 4.
   Prove H^0 = satisfying assignments (theorem: dim_global_sections = |Sol(phi)|).
   This is sound, verified, and does not depend on any unresolved conjectures.

2. Identify the correct obstruction (before committing to more Lean work):
   Test candidate (c) (clause cover nerve) empirically: for small 2-SAT and 3-SAT
   instances, does the Cech H^1 of the clause cover nerve detect unsatisfiability?
   This is a new empirical experiment, much cheaper than the earlier ones.

3. If candidate (c) passes the 2-SAT empirical check: formalize it in Lean 4.

4. Address polynomial-size chain complex construction before any complexity claims.
