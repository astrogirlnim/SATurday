---
name: saturday
description: >
  Unified P vs NP research loop. One skill to run. A Director subagent reads current
  project state and routes to either ORACLE (empirical SAT mining) or proof-sprint
  (Lean sorry-closing). Use this instead of calling those skills separately.
  Invoke when the user says "run saturday", "continue research", or "next session".
---

# SATURDAY: Unified Research Loop

## Purpose

Make compounding progress toward a formal proof of a non-trivial circuit lower bound
in Lean 4, as a concrete step toward P vs NP.

Each session does exactly one of:
- **Mine** — run the ORACLE loop to generate new LRAT-certified lower bound evidence
- **Prove** — run the proof-sprint loop to close one Lean sorry using that evidence

The Director decides which. You never have to choose.

## The Loop

```mermaid
flowchart TD
    load["Step 0\nLoad Context\norchestrator"]
    director["Step 1\nDirector\nsubagent"]
    mine["Step 2A\nORACLE mode\n(empirical mining)"]
    prove["Step 2B\nProof Sprint mode\n(sorry closing)"]
    record["Step 3\nRecorder\norchestrator"]
    commit["Commit + log"]
    loop["Next session?"]

    load --> director
    director -->|"frontier sorrys exist"| prove
    director -->|"no frontier, need data"| mine
    director -->|"both available"| prove
    prove --> record
    mine --> record
    record --> commit
    commit --> loop
    loop -->|"yes"| director
```

---

## Step 0: Load Context (orchestrator — no subagent)

Read these files directly before spawning anything:

- `memory_bank/mmemory_bank_activeContext.md`
- `memory_bank/mmemory_bank_progress.md`
- `search/logs/proof_sprint_log.jsonl` — last entry if exists (`tail -1`)
- `search/logs/oracle_reflections.jsonl` — last entry if exists (`tail -1`)
- `search/logs/guardrail_decisions.jsonl` — last entry if exists (`tail -1`)

Run the sorry inventory:
```bash
cd /Users/nmm/Development/SATurday/theory && \
  grep -rn ":= sorry\|^ *sorry$" --include="*.lean" | grep -v "^Binary"
```

Run the disk check:
```bash
df -h /Users/nmm/Development/SATurday | tail -1
```

If free space is under 3GB: skip any step that would generate large CNF or LRAT files.

Construct `SessionState`:
```json
{
  "sorry_map": [...],
  "last_oracle_action": "...",
  "last_sprint_status": "...",
  "disk_free_gb": <float>
}
```

---

## Step 1: Director (spawn subagent)

```
Task tool call:
  subagent_type: generalPurpose
  description: "Saturday Director"
  prompt: |
    You are the Director of a P vs NP research project using Lean 4 and SAT solvers.

    Read these files first:
      memory_bank/mmemory_bank_activeContext.md
      .cursor/skills/proof-sprint/SKILL.md
      .cursor/skills/run-oracle/SKILL.md

    Current session state:
      {SESSION_STATE_JSON}

    Your job: decide whether this session should run ORACLE (empirical SAT mining)
    or proof-sprint (Lean sorry-closing), and name the single specific target.

    Decision rules (apply in order, first match wins):
    1. If any sorry in sorry_map has all its dependencies proved or axiom-only:
       -> mode = "prove", target = deepest such sorry toward V12.
    2. If last_sprint_status = "stuck" on the same theorem twice:
       -> mode = "mine", target = SAT encoding of the stuck sorry's content.
    3. If last_oracle_action = "PUBLISH" and a new LRAT hash was just anchored:
       -> mode = "prove", target = the sorry that LRAT hash closes.
    4. Default:
       -> mode = "mine", target = next parameter range from active context.

    Return ONLY a JSON block:
    {
      "mode": "prove|mine",
      "target": "<theorem name or SAT instance description>",
      "rationale": "<one sentence>",
      "mode_config": {
        "if_prove": {
          "sorry_file": "<path>",
          "sorry_line": <int>,
          "proof_approach": "<informal sketch, no hyphens>"
        },
        "if_mine": {
          "n": <int>,
          "max_gates": <int>,
          "circuit_class": "monotone|ac0",
          "seed": <int>
        }
      }
    }
```

---

## Step 2A: ORACLE Mode

Follow the steps in `.cursor/skills/run-oracle/SKILL.md` starting at Step 1,
using the `mode_config.if_mine` values from the Director output as the
`parameter_range` for the Planner.

Return the `GuardrailDecision` when done.

---

## Step 2B: Proof Sprint Mode

Follow the steps in `.cursor/skills/proof-sprint/SKILL.md` starting at Step 1
(Navigator), passing the Director's `mode_config.if_prove` values as context
for the Navigator's target selection.

Return the `AttackerOutput` when done.

---

## Step 3: Recorder (orchestrator — no subagent)

Append one line to `search/logs/saturday_sessions.jsonl`:
```json
{
  "session": <N>,
  "mode": "prove|mine",
  "target": "...",
  "outcome": "closed|published|stuck|timeout",
  "barrier_tag": "...",
  "timestamp": <unix>
}
```

If outcome is "closed" or "published":
```bash
cd /Users/nmm/Development/SATurday
git add -f theory/ search/logs/ proofs/
git commit -m "Saturday session <N>: <mode> <target> (<outcome>)"
```

Print a one-paragraph summary to the user:
```
Session <N> complete.
Mode: <prove|mine>
Target: <theorem or SAT instance>
Outcome: <closed|published|stuck|timeout>
Next target: <what the Director would pick next, based on current state>
```

---

## Conventions

**C1 — Barrier tagging.**
Every theorem closed or LRAT anchor committed must carry a barrier tag.
No `unknown` tag is committed without a HITL checkpoint.

**C2 — No silent axioms.**
Every `axiom` added must have a named proof obligation in `EncodingCorrectness.lean`
or a direct analog.

**C3 — One node per session.**
Each session must close or publish at least one node. If zero: log the blocker,
print the HITL prompt from proof-sprint, and stop.

---

## Current Research Chain

```
TARGET: monotone_parity_exponential_lower_bound_v12
  (for all n >= 2, any monotone circuit computing parity-n has size >= 2^(n/4))

Proved base cases:   n = 2, 3, 4, 5, 6, 7, 8  (all C.size > 32, LRAT certified)
AC0 depth table:     n = 3, 4, 5 at depths 2, 3, 4 (UNSAT, LRAT certified)
Open frontier:       andGateSupportFamily, andGateFamilySizeLeCircuitSize
Blocked by frontier: monotone_parity_sunflower_connection
Final goal:          monotone_parity_exponential_lower_bound_v12 (inductive step)
```

---

## Sub-skill Reference

| When... | Use... |
|---|---|
| Frontier sorrys exist | `.cursor/skills/proof-sprint/SKILL.md` |
| No frontier, need SAT data | `.cursor/skills/run-oracle/SKILL.md` |
| Both available | proof-sprint first |
| User says "run saturday" | this file |
