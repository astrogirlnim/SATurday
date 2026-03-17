# ORACLE: Multi-Agent Mathematical Research Loop

Flow diagram for the ORACLE orchestration framework. Each node is either a subagent
(governed by a `.cursor/rules/oracle-agent-*.mdc` file) or a structural element of the loop.

```mermaid
flowchart TD
    START([Run Oracle]) --> CTX
    CTX[Step 0 Load Context] --> DEADLOCK{Deadlock?}
    DEADLOCK -- yes --> HITL1([HITL 1 Ask for new direction])
    HITL1 --> CTX
    DEADLOCK -- no --> PLAN

    PLAN[Step 1 Planner] --> ALG
    PLAN --> GEO
    PLAN --> SKP

    ALG[Step 2a Algebraist]
    GEO[Step 2b Geometer]
    SKP[Step 2c Skeptic]

    ALG --> MINE
    GEO --> MINE
    SKP --> MINE

    MINE[Step 3 Miner] --> REF1
    REF1{Step 4 Reflector - SAT witness?}
    REF1 -- yes --> INVAL[INVALIDATE]
    REF1 -- no --> SELECT[Select best UNSAT]
    SELECT --> FORM

    FORM[Step 5 Formalizer] --> CRIT
    CRIT[Step 6 Critic] --> REF2
    REF2[Step 7 Reflector - Build ReflectionSummary]

    INVAL --> GUARD
    REF2 --> GUARD

    GUARD[Step 8 Guardrail Engine]

    GUARD -- compiled no sorry GOOD --> PUBLISH[PUBLISH]
    GUARD -- CONTINUE --> PLAN
    GUARD -- INVALIDATE --> REDUCE[Reduce n] --> PLAN
    GUARD -- SWITCH STRATEGY --> ROTATE[Rotate bet] --> PLAN
    GUARD -- BLOCKED x3 --> HITL2([HITL 2 All paths relativizing])
    GUARD -- no progress x5 --> HITL3([HITL 3 No delta])
    GUARD -- formalizer failed x3 --> HITL4([HITL 4 Sorry stuck])
    GUARD -- max iterations --> HALT([Exit HALT])

    HITL2 --> PLAN
    HITL3 --> PLAN
    HITL4 --> FORM

    PUBLISH --> GOAL{Goal met?}
    GOAL -- yes --> DONE([Exit Success])
    GOAL -- no --> PLAN

    style ALG fill:#d4e6f1,stroke:#2980b9
    style GEO fill:#d5f5e3,stroke:#27ae60
    style SKP fill:#fde8d8,stroke:#e67e22
    style MINE fill:#f4f6f7,stroke:#7f8c8d
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
    style DONE fill:#d5f5e3,stroke:#1e8449,stroke-width:2px
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
