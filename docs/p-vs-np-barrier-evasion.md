# P vs NP Barrier Evasion Spec (Proof Complexity Ladder)

Primary framework: proof complexity ladder.

Honest position: the classical three barriers were formulated against machine-based
and circuit-based arguments. The ladder's rung statements are combinatorial claims
about syntactic proof systems, so the classical barriers do not directly apply; the
ladder instead faces its own documented limitative results, listed below and treated
with the same severity.

## Relativization

- Claim: rung lower bounds are proved by direct combinatorial analysis of
  derivations (width, bottleneck counting, restrictions), not by simulating machines
  with oracle access. Known resolution lower bounds hold absolutely, not relative to
  an oracle.
- Evasion condition: any rung argument that proceeds by machine simulation robust
  under arbitrary oracles is rejected from the critical path.

## Natural proofs (Razborov-Rudich)

- Claim: rung arguments do not construct large constructive properties of Boolean
  functions; they analyze proofs, not function families. The natural proofs barrier
  formally addresses circuit lower bounds and does not apply verbatim.
- Honest analogue to track: for strong systems (extended Frege and beyond), Krajicek's
  proof complexity generators and Razborov's conjectures indicate lower bounds may
  require breaking cryptographic assumptions, a natural-proofs-like wall. Any R4+
  argument must state why it does not implicitly construct a distinguisher for a
  standard pseudorandom object.

## Algebraization

- Claim: rung arguments do not rely on low-degree extension transfer of machine
  behavior. Same rejection rule as relativization.

## Ladder-specific limitative results (the real walls; must be checked per rung)

- Feasible interpolation death: interpolation proves lower bounds for resolution and
  cutting planes, but provably fails for bounded-depth Frege and stronger systems
  under cryptographic assumptions (Bonet-Pitassi-Raz; Krajicek-Pudlak for extended
  Frege unless RSA is insecure). Any R3+ plan built on interpolation for a strong
  system is rejected.
- Automatability death: resolution is not automatable unless P = NP
  (Atserias-Muller 2019). Consequence for the falsifier: absence of a short proof
  found by search is weak evidence; only size measurements on families with known
  behavior calibrate conjectures.
- Simulation order: lower bounds for a weaker system never transfer upward past a
  system that polynomially simulates it. Every rung must state which known
  simulations sandwich its target system.

## Rejection rule

- If any rung claim lacks a concrete evasion argument for each applicable wall above,
  mark the rung invalid for solve-critical use.
- If an evasion argument is circular or only rhetorical, mark the rung invalid for
  solve-critical use.
- The barrier-auditor skill runs this checklist against every prose proof before
  formalization effort is spent.
