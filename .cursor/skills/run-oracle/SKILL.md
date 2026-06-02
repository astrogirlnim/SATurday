---
name: run-oracle
description: >
  One-cycle ORACLE mining protocol used by saturday when action_type is mine_step.
  Effective roles are Planner, Miner, Formalizer, and Critic. No internal loop.
---

# RUN ORACLE

## Purpose

Execute one empirical research cycle that can produce a SAT or UNSAT result, optional
Lean anchoring, and barrier-aware assessment. Return a single action result to saturday.

## Cycle Contract

- Exactly one cycle.
- No nested iterations.
- Roles: Planner -> Miner -> Formalizer -> Critic.
- Orchestrator writes result and returns.

```mermaid
flowchart LR
    planner[Planner] --> miner[Miner]
    miner --> formalizer[Formalizer]
    formalizer --> critic[Critic]
    critic --> done[ReturnActionResult]
```

## Inputs

`mine_step` config from saturday:

```json
{
  "target": "<instance>",
  "parameter_range": {
    "n": "<int>",
    "max_gates": "<int>",
    "circuit_class": "monotone|ac0|formula",
    "seed": "<int>"
  }
}
```

## Step 0: Context and Safety

Read:

- `memory_bank/mmemory_bank_activeContext.md`
- `infra/config/defaults.yaml`
- `proofs/index.json`
- `search/logs/miner_results.jsonl` (last line if present)

Disk check:

```bash
WORKSPACE=$(git rev-parse --show-toplevel)
df -h "$WORKSPACE" | awk 'NR==2 {print}'
```

If free disk is below 5GB, reduce target size before running Miner.

## Step 1: Planner

Produce one concrete test instance:

```json
{
  "hypothesis": "<falsifiable statement>",
  "instance": {
    "n": "<int>",
    "max_gates": "<int>",
    "circuit_class": "monotone|ac0|formula",
    "seed": "<int>",
    "target_function": "parity|majority|other"
  },
  "success_criteria": "<what counts as progress this cycle>"
}
```

## Step 2: Miner

Generate and solve exactly one CNF instance for the planner output using deterministic seed.

Record one `MinerResult` line in `search/logs/miner_results.jsonl`:

```json
{
  "persona_source": "oracle_single_cycle",
  "n": "<int>",
  "max_gates": "<int>",
  "seed": "<int>",
  "circuit_class": "<class>",
  "target_function": "<function>",
  "outcome": "SAT|UNSAT|TIMEOUT|ERROR",
  "lrat_hash": "<hash_or_null>",
  "solve_time_s": "<float>",
  "cnf_vars": "<int>",
  "cnf_clauses": "<int>",
  "timestamp": "<unix>"
}
```

## Step 3: Formalizer

If `outcome=UNSAT` and `lrat_hash` exists, attempt one Lean anchor theorem update/build.
If not, skip formalization.

Return:

```json
{
  "compiled": "true|false",
  "has_sorry": "true|false",
  "lean_file": "<path_or_null>",
  "lrat_hash": "<hash_or_null>"
}
```

## Step 4: Critic

Run barrier assessment on this cycle outcome:

```json
{
  "relativization": "blocked|evades|unclear",
  "natural_proofs": "blocked|evades|unclear",
  "algebraization": "blocked|evades|unclear",
  "notes": "<one paragraph>"
}
```

Also run adversarial check here (folded skeptic behavior): if evidence indicates
a likely counterexample path, set `result=blocked` and recommend smaller or changed instance.

## Step 5: Return to Saturday

Return exactly:

```json
{
  "status": "success|partial|blocked",
  "artifact_refs": ["<proof_hashes_files_logs>"],
  "barrier_assessment": {
    "relativization": "blocked|evades|unclear",
    "natural_proofs": "blocked|evades|unclear",
    "algebraization": "blocked|evades|unclear"
  },
  "next_recommended_action": "prove_step|mine_step|new_math_step"
}
```

## Invariants

- No multi-iteration control loop here.
- No separate Algebraist/Geometer/Skeptic/Reflector role spawning.
- Deterministic seed and local execution only.
