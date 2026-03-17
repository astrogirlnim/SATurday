# ORACLE: Multi-Agent Mathematical Research Loop

Flow diagram for the ORACLE orchestration framework. Each node is either a subagent
(governed by a `.cursor/rules/oracle-agent-*.mdc` file) or a structural element of the loop.

```mermaid
flowchart TD
    START([Start]) --> CTX

    subgraph STARTUP ["Step 0: Context Ingestion (every run)"]
        CTX["Read memory_bank/\ndocs/ .cursor/rules/\nproofs/index.json\noracle_reflections.jsonl"]
        CTX --> DEADLOCK{Deadlock\ndetected?}
        DEADLOCK -- yes --> HITL1[/"HITL_1\nAsk human for\nnew direction"/]
        HITL1 --> CTX
        DEADLOCK -- no --> PLAN
    end

    subgraph LOOP ["Main Loop (repeats per iteration k)"]

        subgraph PH1 ["Phase 1: Plan"]
            PLAN["Planner\n(Department Chair)\noracle-agent-planner.mdc"]
        end

        PLAN --> PH2

        subgraph PH2 ["Phase 2: Conjecture (parallel)"]
            ALG["Algebraist\n(The Formalist)\noracle-agent-algebraist.mdc\nmodel: mathstral:7b"]
            GEO["Geometer\n(The Visualizer)\noracle-agent-geometer.mdc\nmodel: mathstral:7b"]
            SKP["Skeptic\n(Devil's Advocate)\noracle-agent-skeptic.mdc\nmodel: deepseek-r1:1.5b"]
        end

        PH2 --> PH3

        subgraph PH3 ["Phase 3: Mine (parallel Kissat runs)"]
            MINE["Miner\n(Lab Technician)\noracle-agent-miner.mdc\nKissat + LRAT + SHA256"]
        end

        PH3 --> REF1

        subgraph PH4 ["Phase 4: Aggregate + Formalize"]
            REF1{"Reflector\nPost-Miner\nSAT witness?"}
            REF1 -- "SAT witness found" --> INVAL_EARLY["Signal: INVALIDATE\nlog to counterexamples.jsonl"]
            REF1 -- "all UNSAT" --> SELECT["Select winner\nby composite score"]
            SELECT --> FORM["Formalizer\n(The Proof-Writer)\noracle-agent-formalizer.mdc\nlake build + sorry-closure"]
        end

        FORM --> CRIT

        subgraph PH5 ["Phase 5: Critique"]
            CRIT["Critic\n(Peer Reviewer)\noracle-agent-critic.mdc\n3x barrier profiles\nV13 feedback loop"]
        end

        CRIT --> REF2

        subgraph PH6 ["Phase 6: Reflect"]
            REF2["Reflector\nPost-Critic\noracle-agent-reflector.mdc\nBuild ReflectionSummary\nCompute progress_delta\nWrite oracle_reflections.jsonl"]
        end

        REF2 --> GUARD
        INVAL_EARLY --> GUARD

        subgraph PH7 ["Phase 7: Guardrail Decision"]
            GUARD["Guardrail Engine\n(Ethics Board)\noracle-agent-guardrail.mdc\nWrite guardrail_decisions.jsonl"]
        end

    end

    GUARD -- "compiled + no sorry\n+ lrat valid + grade GOOD" --> PUBLISH
    GUARD -- "CONTINUE" --> PLAN
    GUARD -- "INVALIDATE\nSAT witness" --> REDUCE["Reduce n or\nrestrict class"] --> PLAN
    GUARD -- "SWITCH_STRATEGY\nsame technique x3" --> ROTATE["Rotate bet\nA->B->C->D"] --> PLAN
    GUARD -- "BLOCKED x3 iterations" --> HITL2[/"HITL_2\nAll paths relativizing\nAsk human for\nnon-relativizing technique"/]
    GUARD -- "no progress x5 iterations" --> HITL3[/"HITL_3\nAsk human:\nincrease n, switch bet,\nor provide lemma"/]
    GUARD -- "formalizer failed x3" --> HITL4[/"HITL_4\nAsk human for\nLean proof strategy"/]
    GUARD -- "k >= max_iterations" --> HALT

    HITL2 --> PLAN
    HITL3 --> PLAN
    HITL4 --> FORM

    subgraph TERMINAL ["Terminal Conditions"]
        PUBLISH["PUBLISH\nWrite proofs/index.json\ngit commit\nUpdate checklist"]
        PUBLISH --> GOAL{All success\ncriteria met?}
        GOAL -- yes --> SUCCESS([Exit 0\nResearch goal reached])
        GOAL -- no --> HARDER["Increment n\nor next bet"] --> PLAN
        HALT([Exit 2\nHALT: max iterations])
    end

    subgraph LOGS ["Persistent Logs (written each iteration)"]
        L1["search/logs/oracle_planner.jsonl"]
        L2["search/logs/miner_results.jsonl"]
        L3["search/logs/oracle_reflections.jsonl"]
        L4["search/logs/guardrail_decisions.jsonl"]
        L5["search/logs/counterexamples.jsonl"]
        L6["search/logs/hitl_interventions.jsonl"]
        L7["search/logs/v13_loop_iterations.jsonl"]
        L8["proofs/index.json"]
    end

    subgraph CONTEXT ["Read at Startup"]
        C1["memory_bank/mmemory_bank_projectbrief.md"]
        C2["memory_bank/mmemory_bank_activeContext.md"]
        C3["memory_bank/mmemory_bank_progress.md"]
        C4["memory_bank/mmemory_bank_systemPatterns.md"]
        C5["docs/brainlift/saturday-dev-checklist-v2.md"]
        C6["infra/config/defaults.yaml"]
        C7[".cursor/rules/*.mdc"]
    end

    style ALG fill:#d4e6f1,stroke:#2980b9
    style GEO fill:#d5f5e3,stroke:#27ae60
    style SKP fill:#fde8d8,stroke:#e67e22
    style MINE fill:#f9f9f9,stroke:#7f8c8d
    style FORM fill:#eaf0fb,stroke:#5d6d7e
    style CRIT fill:#fdf2f8,stroke:#8e44ad
    style PLAN fill:#fef9e7,stroke:#f39c12
    style GUARD fill:#f2f3f4,stroke:#2c3e50,stroke-width:2px
    style REF1 fill:#ebf5fb,stroke:#3498db
    style REF2 fill:#ebf5fb,stroke:#3498db
    style HITL1 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style HITL2 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style HITL3 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style HITL4 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style SUCCESS fill:#d5f5e3,stroke:#1e8449,stroke-width:2px
    style HALT fill:#fadbd8,stroke:#922b21,stroke-width:2px
    style PUBLISH fill:#d5f5e3,stroke:#27ae60
```

## Subagent Rule Files

| Subagent | Role | Rule File | Model |
|---|---|---|---|
| Planner | Department Chair | `.cursor/rules/oracle-agent-planner.mdc` | rule-based |
| Algebraist | Formalist | `.cursor/rules/oracle-agent-algebraist.mdc` | mathstral:7b |
| Geometer | Visualizer | `.cursor/rules/oracle-agent-geometer.mdc` | mathstral:7b |
| Skeptic | Devil's Advocate | `.cursor/rules/oracle-agent-skeptic.mdc` | deepseek-r1:1.5b |
| Miner | Lab Technician | `.cursor/rules/oracle-agent-miner.mdc` | deterministic |
| Reflector | Editorial Board | `.cursor/rules/oracle-agent-reflector.mdc` | mathstral:7b |
| Formalizer | Proof-Writer | `.cursor/rules/oracle-agent-formalizer.mdc` | mathstral:7b |
| Critic | Peer Reviewer | `.cursor/rules/oracle-agent-critic.mdc` | rule-based + LLM |
| Guardrail | Ethics Board | `.cursor/rules/oracle-agent-guardrail.mdc` | deterministic |

## Orchestration Entry Point

Skill: `.cursor/skills/run-oracle/SKILL.md`

The skill reads all rule files and drives the loop. No new Python plumbing required.
All existing infrastructure (Kissat, LRAT, Lean 4, Ollama, artifact store) is invoked
via existing CLI commands.
