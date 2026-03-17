# ORACLE: Multi-Agent Mathematical Research Loop

## Main Loop

```mermaid
flowchart LR
    S0[Load Context] --> S1[Planner]
    S1 --> S2[Algebraist]
    S1 --> S3[Geometer]
    S1 --> S4[Skeptic]
    S2 --> S5[Miner]
    S3 --> S5
    S4 --> S5
    S5 --> S6{SAT witness?}
    S6 -- no --> S7[Formalizer]
    S6 -- yes --> S8[Guardrail]
    S7 --> S9[Critic]
    S9 --> S10[Reflector]
    S10 --> S8
    S8 -- continue --> S9[Cleanup]
    S8 -- publish --> S9
    S8 -- halt --> HALT([Halt])
    S9 --> S1

    style S2 fill:#d4e6f1,stroke:#2980b9
    style S3 fill:#d5f5e3,stroke:#27ae60
    style S4 fill:#fde8d8,stroke:#e67e22
    style S5 fill:#f4f6f7,stroke:#7f8c8d
    style S7 fill:#eaf0fb,stroke:#5d6d7e
    style S9 fill:#fdf2f8,stroke:#8e44ad
    style S1 fill:#fef9e7,stroke:#f39c12
    style S8 fill:#f2f3f4,stroke:#2c3e50,stroke-width:2px
    style DONE fill:#d5f5e3,stroke:#1e8449,stroke-width:2px
    style HALT fill:#fadbd8,stroke:#922b21,stroke-width:2px
```

## Guardrail Decisions

```mermaid
flowchart LR
    G[Guardrail] --> D1{Decision}
    D1 -- compiled and verified --> PUBLISH[Publish and commit]
    D1 -- continue --> LOOP[Next iteration]
    D1 -- SAT witness --> REDUCE[Reduce n]
    D1 -- same technique x3 --> ROTATE[Rotate bet]
    D1 -- blocked x3 --> H2([HITL 2])
    D1 -- no progress x5 --> H3([HITL 3])
    D1 -- sorry stuck x3 --> H4([HITL 4])
    D1 -- max iterations --> HALT([Halt])

    PUBLISH --> GOAL{All goals met?}
    GOAL -- yes --> DONE([Exit success])
    GOAL -- no --> LOOP

    REDUCE --> LOOP
    ROTATE --> LOOP
    H2 --> LOOP
    H3 --> LOOP
    H4 --> LOOP

    style H2 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style H3 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style H4 fill:#fdedec,stroke:#c0392b,stroke-width:2px
    style PUBLISH fill:#d5f5e3,stroke:#27ae60
    style DONE fill:#d5f5e3,stroke:#1e8449,stroke-width:2px
    style HALT fill:#fadbd8,stroke:#922b21,stroke-width:2px
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
