---
name: run-oracle
description: Runs the ORACLE multi-agent mathematical research loop. Coordinates 9 subagents (Planner, Algebraist, Geometer, Skeptic, Miner, Reflector, Formalizer, Critic, Guardrail) in a reflection loop with HITL escalation. Use when asked to run the research loop, advance a mathematical conjecture, explore a research bet, or when the user says "run oracle", "start the loop", or "continue research".
---

# ORACLE: Multi-Agent Mathematical Research Loop

Works for any formal math research project. Reads project context at startup.
Runs until a goal is reached, a HALT condition fires, or a human is needed.

## Flow Overview

```mermaid
flowchart TD
    START([Run Oracle]) --> S0

    subgraph S0 ["Step 0: Load Context"]
        CTX["Read memory_bank/ + docs/\n.cursor/rules/ + proofs/index.json\noracle_reflections.jsonl"]
        CTX --> DL{Deadlock?}
        DL -- yes --> H1[/"HITL_1\nAsk: new direction"/]
        H1 --> CTX
        DL -- no --> S1
    end

    subgraph S1 ["Step 1: Plan"]
        PLAN["Planner\noracle-agent-planner.mdc\nProduces IterationPlan\nhypothesis + 3 persona tasks"]
    end

    S1 --> S2

    subgraph S2 ["Step 2: Conjecture — parallel"]
        ALG["Algebraist\nmathstral:7b\nPolynomial framing"]
        GEO["Geometer\nmathstral:7b\nCombinatorial framing"]
        SKP["Skeptic\ndeepseek-r1:1.5b\nAdversarial — find SAT"]
    end

    S2 --> S3

    subgraph S3 ["Step 3: Mine — parallel Kissat"]
        MINE["Miner\noracle-agent-miner.mdc\nKissat + LRAT + SHA256\n3x MinerResult"]
    end

    S3 --> S4

    subgraph S4 ["Step 4: Aggregate (Reflector pass 1)"]
        R1{"SAT witness\nfrom Skeptic?"}
        R1 -- yes --> INVAL["INVALIDATE\nlog counterexamples.jsonl\nskip formalize"]
        R1 -- no --> SEL["Rank UNSAT results\nselect winner"]
    end

    SEL --> S5

    subgraph S5 ["Step 5: Formalize"]
        FORM["Formalizer\noracle-agent-formalizer.mdc\nlake build + sorry-closure\nup to 3 LLM attempts"]
    end

    S5 --> S6

    subgraph S6 ["Step 6: Critique"]
        CRIT["Critic\noracle-agent-critic.mdc\n3x barrier profiles\nV13 feedback loop"]
    end

    S6 --> S7

    subgraph S7 ["Step 7: Reflect (Reflector pass 2)"]
        REF["Reflector\nBuild ReflectionSummary\ncompute progress_delta\nwrite oracle_reflections.jsonl"]
    end

    INVAL --> S8
    S7 --> S8

    subgraph S8 ["Step 8: Guardrail Decision"]
        G["Guardrail Engine\noracle-agent-guardrail.mdc\nwrite guardrail_decisions.jsonl"]
    end

    G -- "compiled + no sorry\n+ lrat valid + grade GOOD" --> PUB["PUBLISH\nupdate proofs/index.json\ngit commit"]
    G -- "CONTINUE" --> S1
    G -- "INVALIDATE" --> LESS["Reduce n\nor restrict class"] --> S1
    G -- "SWITCH_STRATEGY\nsame technique x3" --> ROT["Rotate bet\nA->B->C->D"] --> S1
    G -- "BLOCKED x3 iters" --> H2[/"HITL_2\nAll paths relativizing\nAsk: non-relativizing technique"/]
    G -- "no progress x5 iters" --> H3[/"HITL_3\nAsk: increase n, switch bet,\nor provide lemma"/]
    G -- "formalizer failed x3" --> H4[/"HITL_4\nAsk: Lean proof strategy"/]
    G -- "k >= max_iterations" --> HALT([Exit 2: HALT])

    H2 --> S1
    H3 --> S1
    H4 --> S5

    PUB --> GOAL{All success\ncriteria met?}
    GOAL -- yes --> DONE([Exit 0: Goal reached])
    GOAL -- no --> HARDER["Increment n"] --> S1

    style ALG fill:#d4e6f1,stroke:#2980b9
    style GEO fill:#d5f5e3,stroke:#27ae60
    style SKP fill:#fde8d8,stroke:#e67e22
    style MINE fill:#f4f6f7,stroke:#7f8c8d
    style FORM fill:#eaf0fb,stroke:#5d6d7e
    style CRIT fill:#fdf2f8,stroke:#8e44ad
    style PLAN fill:#fef9e7,stroke:#f39c12
    style G fill:#f2f3f4,stroke:#2c3e50,stroke-width:2px
    style H1 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style H2 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style H3 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style H4 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style DONE fill:#d5f5e3,stroke:#1e8449,stroke-width:2px
    style HALT fill:#fadbd8,stroke:#922b21,stroke-width:2px
    style PUB fill:#d5f5e3,stroke:#27ae60
```

## Step 0: Load Context (always first)

Read these files before anything else:

- `memory_bank/mmemory_bank_projectbrief.md` -> problem_statement, success_criteria
- `memory_bank/mmemory_bank_activeContext.md` -> current_progress, open_tasks
- `memory_bank/mmemory_bank_progress.md` -> what works, known failures
- `memory_bank/mmemory_bank_systemPatterns.md` -> architecture constraints
- `docs/brainlift/saturday-dev-checklist-v2.md` -> open conjectures
- `infra/config/defaults.yaml` -> system config (models, seeds, max_n)
- `.cursor/rules/*.mdc` -> behavioral constraints (no emojis, no cloud, etc.)
- `search/logs/oracle_reflections.jsonl` -> last entry (prior iteration state)
- `search/logs/guardrail_decisions.jsonl` -> last entry (prior decision)
- `proofs/index.json` -> verified artifact inventory

Construct `ResearchContext` mentally. If `oracle_reflections.jsonl` has no entries,
this is iteration 0 (fresh start).

Check for immediate deadlock: if `known_barriers` shows all bets blocked with no
open conjectures, trigger **HITL_1** before starting the loop.

## Step 1: Plan (invoke oracle-agent-planner rule)

Read `.cursor/rules/oracle-agent-planner.mdc`. Follow it exactly.

Produce `IterationPlan` with:
- A falsifiable `hypothesis`
- Three distinct `persona_assignments` (algebraist task / geometer task / skeptic task)
- A `parameter_range` (specific n values, not open-ended)
- A `fallback_strategy`

Log to `search/logs/oracle_planner.jsonl`.

## Step 2: Generate Conjectures in Parallel (3 subagents)

Invoke all three persona rules. Run their tasks concurrently (3 parallel tool calls).

**Algebraist** - read `.cursor/rules/oracle-agent-algebraist.mdc`
Run: `python -c "from search.agents.conjecturer import AlgebraistPersona; ..."`
Or invoke existing `satday mine` with algebraic framing.

**Geometer** - read `.cursor/rules/oracle-agent-geometer.mdc`
Run: `python -c "from search.agents.conjecturer import GeometerPersona; ..."`

**Skeptic** - read `.cursor/rules/oracle-agent-skeptic.mdc`
Run: `python -c "from search.agents.conjecturer import SkepticPersona; ..."`
Note: Skeptic's CNF asks if a circuit EXISTS (adversarial), not that none exists.

Each produces: `{lean_stub, cnf_spec, proof_sketch, barrier_risk}` or `{cnf_spec}` for Skeptic.

## Step 3: Mine (invoke oracle-agent-miner rule)

Read `.cursor/rules/oracle-agent-miner.mdc`. Follow it exactly.

Run Kissat on all 3 CNF specs. Use existing infrastructure:
```bash
python -m search.agents.miner --config infra/config/defaults.yaml --spec {cnf_spec_path}
```
Or invoke the supervisor with the 3 specs in sequence.

Collect 3x `MinerResult`. Log to `search/logs/miner_results.jsonl`.

## Step 4: Aggregate (first Reflector pass)

Read `.cursor/rules/oracle-agent-reflector.mdc`, section "First Invocation: Post-Miner".

**If Skeptic returned SAT**: write to `search/logs/counterexamples.jsonl`, skip to Step 7
with decision=INVALIDATE.

**If all UNSAT**: rank by composite score, select winner for Formalizer.

## Step 5: Formalize (invoke oracle-agent-formalizer rule)

Read `.cursor/rules/oracle-agent-formalizer.mdc`. Follow it exactly.

Run:
```bash
python -m search.agents.formalizer --lrat-hash {hash} --hypothesis "{hypothesis}"
lake build {lean_file}
```

Produce `FormalResult`. If sorry present after 3 LLM attempts, mark `llm_attempts=3`.

## Step 6: Critique (invoke oracle-agent-critic rule)

Read `.cursor/rules/oracle-agent-critic.mdc`. Follow it exactly.

Pass ALL 3 ConjectureOutputs (not just the winner) to the Critic.
Run existing critic agent:
```bash
python -m search.agents.critic --proofs {all_three_lean_stubs} --report
```

Produce `CriticReport` with barrier profiles for all 3 approaches.

## Step 7: Reflect (second Reflector pass)

Read `.cursor/rules/oracle-agent-reflector.mdc`, section "Second Invocation: Post-Critic".

Build `ReflectionSummary`. Compute `progress_delta` vs. prior JSONL entry.
Write to `search/logs/oracle_reflections.jsonl`.

## Step 8: Guardrail Decision

Read `.cursor/rules/oracle-agent-guardrail.mdc`. Follow decision table exactly.

Write decision to `search/logs/guardrail_decisions.jsonl`.

Then execute the decision:

### PUBLISH
```bash
# Update proofs/index.json with new artifact
python search/tools/inspect_artifacts.py --register {lrat_hash}
# Commit
git add theory/Conjectures/ proofs/ search/logs/
git commit -m "Verify: {theorem_name} n={n} lrat={lrat_hash[:8]}"
# Update checklist
# Check if all success_criteria met -> if yes, print summary and EXIT
# If not, increment n and loop back to Step 1
```

### CONTINUE
Loop back to Step 1 with updated ResearchContext (inject ReflectionSummary).

### INVALIDATE
Reduce n by 1 (or restrict circuit class). Loop back to Step 1.

### SWITCH_STRATEGY
Rotate bet (A->B->C->D->A). Loop back to Step 1.

### HALT
```bash
# Write halt report
python search/reporting/md_reporter.py --halt --output docs/reports/halt_report_{timestamp}.md
git add docs/reports/ search/logs/
git commit -m "HALT: oracle loop exhausted after {k} iterations"
```
Print summary. Exit.

### HITL_1 through HITL_4
Print the specific prompt from the Guardrail rule (verbatim, do not paraphrase).
Wait for human input. Log response to `search/logs/hitl_interventions.jsonl`.
Inject response at the appropriate phase and continue loop.

## Loop Invariants (check every iteration)

- [ ] Every Kissat run used a fixed seed from IterationPlan.parameter_range.seed
- [ ] Every LRAT hash was verified by the LRAT checker before being accepted
- [ ] No cloud APIs were called (zero_cost_guard.py enforces this)
- [ ] All LLM calls used Ollama local models only
- [ ] ReflectionSummary was written to JSONL before GuardrailEngine ran
- [ ] GuardrailEngine decision was written to JSONL before acting on it

## Persona Rule Reference

| Phase | Subagent | Rule File |
|---|---|---|
| 1 | Planner | `.cursor/rules/oracle-agent-planner.mdc` |
| 2a | Algebraist | `.cursor/rules/oracle-agent-algebraist.mdc` |
| 2b | Geometer | `.cursor/rules/oracle-agent-geometer.mdc` |
| 2c | Skeptic | `.cursor/rules/oracle-agent-skeptic.mdc` |
| 3 | Miner | `.cursor/rules/oracle-agent-miner.mdc` |
| 4,7 | Reflector | `.cursor/rules/oracle-agent-reflector.mdc` |
| 5 | Formalizer | `.cursor/rules/oracle-agent-formalizer.mdc` |
| 6 | Critic | `.cursor/rules/oracle-agent-critic.mdc` |
| 8 | Guardrail | `.cursor/rules/oracle-agent-guardrail.mdc` |

## Adapting to a Different Math Problem

Replace the memory bank files with those for the new project.
The loop structure, persona roles, guardrail conditions, and HITL triggers
are all project-agnostic. The only project-specific coupling is:
- `problem_statement` (from projectbrief.md)
- `oracle_type` (Kissat for SAT problems; swap for SMT/Groebner/other for different domains)
- `formal_verifier` (Lean 4 here; swap for Coq/Isabelle for other projects)
