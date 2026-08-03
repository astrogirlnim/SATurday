# P vs NP Main Attack Lock

Locked: 2026-08-03 (reboot). Replaces the sheaf-cohomological lock of 2026-06-02,
which was invalid because its core lemma had already failed its falsification tests
in April 2026 (see docs/postmortems/sheaf-and-kolmogorov-closure.md).

Primary framework (locked):

- Proof complexity ladder: super-polynomial lower bounds for successively stronger
  propositional proof systems, each certified in Lean.

Summit link (a theorem, not a hope):

- Cook and Reckhow 1979: a polynomially bounded propositional proof system exists
  if and only if NP = coNP.
- P = NP implies NP = coNP. Contrapositive chain: super-polynomial lower bounds for
  all propositional proof systems imply NP != coNP, which implies P != NP.
- Until the bridge is formalized (rung R5), it is recorded here as an explicitly
  informal, literature-cited implication. It is never encoded as a Lean axiom.

One-line falsifiable claim:

- For each rung system S in the ladder there is an explicit CNF family whose
  S-refutations require super-polynomial size; each established rung is certified
  in Lean with zero sorries and standard axioms only.

Per-rung falsification: exhibiting polynomial-size S-proofs for the rung's chosen
hard family kills that rung's target family and forces a family change or rung
redesign. Exhibiting a polynomially bounded proof system kills the program and
proves NP = coNP.

Freeze policy:

- Non-primary directions are frozen by default: Boolean circuit lower bounds,
  algebraic circuit lower bounds (VP vs VNP), sheaf and topological invariants,
  Kolmogorov complexity arguments, logic and descriptive complexity branches.
- A frozen branch may reopen only if:
  - it provides a concrete counterexample to the current primary claim, or
  - it supplies a formal lemma that strictly shortens the current primary critical
    path, or
  - the barrier audit shows the current rung is provably unreachable with all known
    ladder techniques and the branch offers a technique that survives the same audit.
- Any new lock requires a falsification-evidence review: the lock document must cite
  the current empirical and formal evidence for the core new claim, and a lock that
  contradicts recorded refutations is invalid.
