# P vs NP Barrier Evasion Spec

Primary framework: sheaf-cohomological obstruction on SAT-instance structure.

## Relativization

- Claim: target invariants are built from instance-local structural data (clause and assignment topology), not from oracle query transcripts.
- Evasion condition: any argument step that remains valid under arbitrary oracle access is rejected from the critical path unless it is explicitly non-decisive.

## Natural Proofs

- Claim: the primary invariant is instance-specific and not a large constructive property over broad function families.
- Evasion condition: if a proposed lemma implies a large constructive classifier for many Boolean function families, that lemma is rejected from the critical path.

## Algebraization

- Claim: the primary objects are combinatorial/topological sheaf constructions and do not rely on low-degree algebraic extension as the main proving mechanism.
- Evasion condition: any step whose validity depends on black-box low-degree extension transfer is rejected from the critical path unless a non-algebraizing refinement is provided.

## Rejection Rule

- If any major claim lacks a concrete evasion argument for one barrier, mark the direction invalid for solve-critical use.
- If an evasion argument is circular or only rhetorical, mark the direction invalid for solve-critical use.
