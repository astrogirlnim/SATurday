# P vs NP Proof Standards

These standards define what counts as an accepted solve-quality proof in this repo.

- Every critical claim must be formalized in Lean or reduced to an already formalized lemma.
- No new axioms are allowed on the critical path to `P != NP` or `P = NP`.
- No heuristic-only step may justify theorem-level conclusions.
- Barrier evasion must be explicit for relativization, natural proofs, and algebraization.
- All randomness-dependent empirical claims must be deterministic and replayable.
- Every generated artifact must be hash-addressed and reproducible locally.
- Any unresolved dependency blocks acceptance of a final proof claim.

Minimum acceptance gate:

- Complete implication chain from definitions to final theorem.
- Independent internal red-team pass with no unresolved critical objections.
- Deterministic rerun reproducing the same proof artifacts.
