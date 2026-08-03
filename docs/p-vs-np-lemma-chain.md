# P vs NP Core Lemma Chain

Primary framework: sheaf-cohomological obstruction on SAT-instance structure.

Final theorem target:

- `ClassP != ClassNP` in `theory/Theory/PvsNPGoal.lean`.

Minimum lemma sequence (critical path):

1. **Lemma L1 (definition bridge, known)**  
   For each SAT instance `I`, construct a finite combinatorial site `Site(I)` and sheaf `F(I)` such that global sections `Γ(F(I))` are exactly satisfying assignments of `I`.

2. **Lemma L2 (algorithmic extraction boundary, adaptation)**  
   Any polynomial-time witness-construction procedure for `I` induces a uniformly bounded extraction morphism on `F(I)` over `Site(I)`.

3. **Lemma L3 (cohomological obstruction, new)**  
   There exists an infinite SAT-instance family `{I_n}` where nontrivial obstruction class `Obs(I_n)` blocks any uniformly bounded extraction morphism while `Γ(F(I_n))` remains nonempty.

4. **Lemma L4 (complexity lift, adaptation)**  
   If such an obstruction family `{I_n}` exists, then witness existence and polynomial-time witness construction separate on that family.

5. **Lemma L5 (class separation, adaptation)**  
   Separation on the family lifts to language-level class separation, yielding `ClassP != ClassNP`.

Lemma classification table:

- `L1`: known (definition-level equivalence target, standard sheaf-style encoding pattern).
- `L2`: adaptation (translate algorithmic uniformity into morphism bound).
- `L3`: new (core obstruction existence claim).
- `L4`: adaptation (bridge from obstruction behavior to search hardness separation).
- `L5`: adaptation (standard lift from family hardness to class-level inequality).

Immediate falsification tests for each new lemma:

- `L3` falsification test T3.1: construct bounded extraction morphism for candidate family; if successful on infinitely many `I_n`, `L3` is false.
- `L3` falsification test T3.2: compute candidate obstruction class for small seeded family and check triviality; if always trivial under intended construction, `L3` is false.

Lean-precision filter (must pass before lemma stays on critical path):

- Keep lemma only if it can be stated with explicit finite objects and quantifiers over definable structures.
- Reject lemma if it requires undefined analytic objects, nonconstructive existence without finite witness schema, or implicit semantic shortcuts not representable in Lean.
- Current precision status:
  - `L1`: pass (finite-object definitional statement).
  - `L2`: pass (bounded morphism statement over explicit structures).
  - `L3`: pass (existential family with explicit obstruction predicate, proof open).
  - `L4`: pass (implication form over explicit predicates).
  - `L5`: pass (class-level implication form already aligned with target module).
