---
name: proof-sprint
description: >
  One-cycle frontier proof action used by saturday when action_type is prove_step.
  Attempts to close exactly one Lean node and returns a single result payload.
---

# PROOF SPRINT

## Purpose

Close one frontier theorem node toward `monotone_parity_exponential_lower_bound_v12`
with a bounded attempt budget and no internal session loop.

## Cycle Contract

- Exactly one chosen frontier node.
- Up to three proof attempts.
- Return one result payload and stop.

```mermaid
flowchart LR
    load[LoadContext] --> pick[SelectFrontierNode]
    pick --> attempt[AttemptProof]
    attempt --> record[RecordOutcome]
    record --> done[ReturnActionResult]
```

## Step 0: Load Context

Read:

- `memory_bank/mmemory_bank_activeContext.md`
- `theory/Conjectures/BetA/Proofs/MonotoneParityInductive.lean`
- `theory/Theory/Sunflower.lean`
- `.cursor/rules/lean4-development.mdc`

Inventory sorry nodes:

```bash
WORKSPACE=$(git rev-parse --show-toplevel)
cd "$WORKSPACE/theory" && rg ":= sorry|^ *sorry$" --glob "*.lean"
```

Build:

```json
{
  "sorry_map": [{"file":"<path>","line":"<int>","theorem":"<name>"}]
}
```

## Step 1: Select Frontier Node

Pick one node by priority:

1. Deepest dependency node on the V12 path with all dependencies already proved or axiom-backed.
2. Lowest expected proof complexity tie-break.

Output:

```json
{
  "theorem_name": "<name>",
  "file": "<path>",
  "line": "<int>",
  "barrier_tag": "relativization_safe|natural_proof_safe|algebraization_safe|unknown",
  "approach": "<brief tactic plan>"
}
```

## Step 2: Attempt Proof

Run up to three distinct attempts. After each attempt, build only relevant module or full project.

If the node is SAT-reducible and Lean tactics are not productive, emit blocker and recommend `mine_step`.

Result:

```json
{
  "theorem_name": "<name>",
  "status": "closed|stuck",
  "attempts": "<int>",
  "barrier_tag": "<tag>",
  "blocker": "<null_or_reason>"
}
```

## Step 3: Record Outcome

Append one line to `search/logs/proof_sprint_log.jsonl`:

```json
{
  "theorem": "<name>",
  "status": "closed|stuck",
  "attempts": "<int>",
  "barrier_tag": "<tag>",
  "timestamp": "<unix>"
}
```

## Step 4: Return to Saturday

Return exactly:

```json
{
  "status": "success|partial|blocked",
  "artifact_refs": ["<edited_files_or_hashes>"],
  "barrier_assessment": {
    "relativization": "blocked|evades|unclear",
    "natural_proofs": "blocked|evades|unclear",
    "algebraization": "blocked|evades|unclear"
  },
  "next_recommended_action": "prove_step|mine_step|new_math_step"
}
```

Mapping:

- `closed` -> `success`
- `stuck` but with concrete SAT encoding path -> `partial`, recommend `mine_step`
- `stuck` without concrete path -> `blocked`, recommend `new_math_step` or later `prove_step`

## Invariants

- One node per session.
- No nested prove loops.
- No silent new axioms without explicit proof obligation notes.
