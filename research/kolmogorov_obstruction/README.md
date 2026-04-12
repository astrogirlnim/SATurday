# Kolmogorov Obstruction to Polynomial Search

## Status
Parked. Superseded by sheaf_cohomological_obstruction (session 2026-04-12).
Revisit if the sheaf approach hits a hard block.

## One-line description
Show that if P = NP, there exists a polynomial-time near-optimal compressor of
NP witnesses given instances; derive a contradiction from known incompressibility
results at specific instance lengths.

## Core insight
Existing meta-complexity work (MCSP) measures Kolmogorov complexity of
exponentially long function truth tables. This approach instead measures
K(w|I) for polynomial-length individual instances I and witnesses w. Because
Kolmogorov complexity is uncomputable, the Razborov-Rudich natural proofs barrier
(which requires efficiently computable distinguishing properties) does not apply.

## Barrier evasion claimed
Relativization: K(w|I) is defined relative to a fixed universal machine, not an
  oracle. Partial foothold remains: oracle-relativized K is well-defined and the
  contradiction must be shown not to reproduce in relativized worlds. UNRESOLVED.
Natural proofs: K is Pi-0-2-complete and uncomputable. Razborov-Rudich
  constructivity condition fails immediately and categorically.
Algebraization: K is defined over individual binary strings. No low-degree
  polynomial extension preserves incompressibility properties. Plausible but not
  formally proven.

## Why this approach was parked
Fatal structural gap: K(w|I) large does not imply no poly-time machine outputs w.
Information content and computation time are orthogonal. Proving the bridge theorem
between descriptive hardness and computational hardness would itself require a
result at least as hard as P vs NP. The approach also requires an explicit NP
language where every witness has high K, and no such explicit language is known.

## First Lean target (if revisited)
Formalize Levin's optimal search theorem. Then state: if SAT is in P then for all
epsilon > 0, there exists a poly-time A such that |A(x)| <= K(x) + epsilon * n.

## Key references
Levin (1973): optimal search theorem.
Allender, Hirahara (2017-2022): MCSP and resource-bounded Kolmogorov complexity.
Hirahara (2021): Non-Black-Box Worst-Case to Average-Case Reductions within NP.
Razborov and Rudich (1997): natural proofs barrier.
Baker, Gill, Solovay (1975): relativization barrier.
