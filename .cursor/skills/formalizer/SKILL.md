---
name: formalizer
description: >
  One-cycle Lean formalization push used by saturday when action_type is formalize.
  Converts a gate-accepted prose argument into Lean meeting the acceptance bar:
  compiles, zero sorries, standard axioms only, verified by scripts/check_axioms.sh.
---

# FORMALIZER

## Purpose

Turn an accepted prose argument into a machine-checkable certificate. A result
exists only when this skill finishes green.

## Contract

- Input: one rung with a prose argument whose accept_prose gate has passed, or an
  explicitly scoped statement-only task (stating a Frontier target).
- Exactly one Lean module or one theorem cluster per invocation.
- Up to three proof engineering attempts on the same obligation; then return
  partial or blocked with the exact failing obligation quoted.
- No new axioms, ever. External tool trust is never converted into an axiom.
- Work-in-progress statements go in a namespace ending in Frontier and may carry
  sorry; accepted modules never import Frontier content.

## Procedure

1. Read the prose argument in the rung memory and the existing modules under
   `theory/Theory/ProofComplexity/`.
2. Write or extend the Lean module. Definitions first, statement second, proof
   third. Prefer mathlib idioms; search mathlib before defining anything.
3. Build:

```bash
WORKSPACE=$(git rev-parse --show-toplevel)
cd "$WORKSPACE/theory" && lake build
```

4. Gate (must pass for acceptance):

```bash
WORKSPACE=$(git rev-parse --show-toplevel)
"$WORKSPACE/scripts/check_axioms.sh"
```

   The gate runs lake build, rejects sorries outside Frontier namespaces, and
   rejects any axiom outside propext, Classical.choice, Quot.sound for the
   declarations listed in scripts/accepted_declarations.txt.

5. On success: add the new accepted declarations to
   scripts/accepted_declarations.txt, rerun the gate, and record the module path
   and declaration names in the rung memory.

## Return payload

```json
{
  "status": "success|partial|blocked",
  "artifact_refs": ["theory/Theory/ProofComplexity/<Module>.lean"],
  "notes": "<what compiled, what the gate reported, or the exact failing obligation>",
  "next_recommended_action": "formalize|prove|falsify|audit"
}
```

Status mapping: gate green on the full target maps to success and a pending
merge_certified human gate; compiles with Frontier sorries remaining maps to
partial; a specific unprovable obligation maps to blocked and the obligation is
quoted verbatim in the rung memory for the next prover cycle.

## Style

- Comment the mathematical intent of every definition and nontrivial proof step.
- Generated prose avoids hyphens as punctuation; spell connections in words.
