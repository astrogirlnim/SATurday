# Postmortem: Sheaf-Cohomological and Kolmogorov Obstruction Approaches (Closed)

Date closed: 2026-08-03
Disposition: archived to `archive/research/sheaf_cohomological_obstruction/`,
`archive/research/kolmogorov_obstruction/`, and `archive/theory/SheafApproach/`.

## Sheaf-cohomological obstruction

The attack: find an instance-level sheaf invariant separating SAT witness existence
from polynomial-time witness construction (lemma chain L1 to L5 in the June docs).

What happened:

- L1 was real and was proved: global sections of the satisfaction sheaf correspond to
  satisfying assignments (H0 result, archived in `SatisfactionSheaf.lean`). This is a
  definitional bridge, not an obstruction.
- The core new lemma (L3, nontrivial obstruction class blocking bounded extraction)
  failed its own falsification tests in April 2026:
  - 1-skeleton constructions produced H1 nonzero at all clause-to-variable ratios
    (no phase transition, no SAT signal).
  - Full nerve constructions produced H1 always zero.
  - The clause-cover nerve variant also failed, closing the empirical phase
    (commit ef82a98).
- Theoretical accompaniment: any polynomial-time syntactic sheaf construction that
  detected satisfiability would itself be a polynomial-time SAT decision procedure,
  so the invariant cannot be both computable and decisive in the intended way.

Despite this, the June 2026 session locked sheaf cohomology as the primary attack.
That lock contradicted the repo's own stop conditions (a direction that fails
explicit adversarial attempts 3 times must stop). Process failure, now corrected:
locks require a falsification-evidence review first.

## Kolmogorov obstruction

Fatal gap identified at triage: K(w|I) being large for witnesses w does not imply
computational hardness of finding some witness. No bridge from incompressibility to
lower bounds was found. Parked in April, closed now.

## Lessons (now enforced)

1. A main attack lock must cite the current falsification evidence for its core new
   lemma; a lock that contradicts recorded refutations is invalid.
2. Definitional bridges (L1-style results) are not progress on obstructions; rungs on
   the ladder must be lower-bound statements, not reformulations.
3. Negative results are recorded and archived, not deleted: the empirical H1 data and
   scripts remain in the archive for future reference.
