# Active Context: Current Work and Next Steps

## Last Updated: 2026-01-28

## Recent Work (Last Two Sessions)

### Session 1: V4 Encoding Scalability + V3 Baseline Extension

**V4 (Streaming Truth Table) — COMPLETE:**
- Implemented streaming truth table encoding in `search/circuits/synthesis.py`
  - New method `_encode_streaming_parity`: generates clauses row-by-row, never loads full 2^n table into memory
  - New method `_encode_single_row_streaming`: encodes one truth table row with fresh per-row variables
  - `encode_synthesis` now accepts `encoding_mode: str` ("explicit" or "streaming") and `target_function: Optional[str]`
- Modified `search/agents/miner.py`:
  - Auto-selects encoding mode: `streaming` for parity with n > 10, `explicit` otherwise
  - Added `_generate_truth_table` helper for n <= 10
- Modified `search/templates/bet_a_circuits.py`:
  - Changed threshold for empty truth table return from `n > 8` to `n > 10`
- Modified `search/agents/planner.py`:
  - `_generate_size_progression` now respects explicit `step` param from config (was ignoring it)

**V3 Extension (n=11-15) — COMPLETE:**
- Created `infra/config/bet_a_v3_extension.yaml` for n=11-15 run
- Successfully generated 9 instances: all UNSAT
- Metrics:
  - n=11: 72K vars, 1.07M clauses, 20MB, ~15s, UNSAT
  - n=13: 331K vars, 4.96M clauses, 96MB, ~40s, UNSAT
  - n=15: 1.42M vars, 21.5M clauses, 446MB, ~50s, UNSAT
- n=16-20 deferred: streaming produces 2GB+ CNFs per instance (impractical)

**Storage Cleanup:**
- Deleted all CNFs > 1MB (n=11-15 CNFs deleted post-verification)
- Deleted all LRATs not referenced by the 3 verified Lean proofs (n=2, n=3, n=4)
- Deleted 315 generated run reports from `docs/reports/`
- `proofs/` directory: 15GB -> 28MB
- Git commit: "Delete 315 generated run reports - noise with no research value" (9af64f4)

### Session 2: Roadmap Review + Checklist Update

**Strategic Review:**
- Re-read project-concept.md, mvp-critique.md, market-analysis.md, agent-recommendations.md
- Produced honest gap analysis: pipeline is a reproducer, not an explorer — the LLM Conjecturer is the missing intelligence layer

**Checklist Updated (`docs/brainlift/saturday-dev-checklist-v2.md`):**
- Added V4b: Algebraic Parity Encoding (O(n) clauses, unblocks n=16-20)
- Added V9: LLM Conjecturer Activation (DeepSeek-Prover-V2-7B via Ollama/MLX)
- Added V10: Real Barrier Analysis in Critic Agent (oracle-world diagnostics)
- Updated Priority Classification with dependency order
- Git commit: "Add V4b, V9, V10 to checklist: algebraic encoding, LLM conjecturer, real barrier analysis" (e822537)

---

## Current State

### What Works

1. Full agent pipeline: Planner -> Conjecturer -> Miner -> Formalizer -> Critic
2. Multi-circuit synthesis: monotone, AC0, formula circuits
3. Multi-function templates: parity, majority, threshold-2, threshold-3 (7 templates total)
4. Streaming encoding: handles parity n=11-15 without loading full truth table
5. SAT solving with LRAT proof extraction (Kissat, ARM64)
6. Content-addressed artifact store (SHA256)
7. Verified proofs: 3 complete Lean theorems (n=2, n=3, n=4 monotone parity)
8. Lean infrastructure: circuit semantics, LRAT-Lean axiom, tactic library

### What's Missing (The Honest Gap)

1. **LLM Conjecturer** (V9) — R2 is template-only; no LLM integration exists yet
   - System explores a fixed search space rather than proposing novel conjectures
   - This is the single highest-leverage item to activate
2. **Algebraic encoding** (V4b) — streaming still produces O(2^n) clauses; n=16-20 blocked
3. **Bets B, C, D** (V6, V7, V8) — not started
4. **Real barrier analysis** (V10) — R5 is heuristic tagging only, no oracle-world diagnostics
5. **Publication package** (V5) — not started

---

## Next Steps (Dependency Order)

### V4b: Algebraic Parity Encoding (Immediate Unblock)
- Replace streaming truth table with XOR-constraint encoding: O(n) clauses instead of O(2^n)
- Use auxiliary variables for XOR chains without enumerating rows
- Target: n=16 CNF under 10MB, solve within 60s
- Unblocks: V3 n=16-20, all large-n work

### V9: LLM Conjecturer Activation (Highest Leverage)
- Pull DeepSeek-Prover-V2-7B locally via Ollama or MLX
- Replace template generation in ConjecturerAgent with LLM prompting
- Feed existing verified results (n=2-4) as grounding context
- Implement prompt-response caching
- Acceptance: one LLM-proposed conjecture survives Miner + compiles in Lean

### V10: Real Barrier Analysis (After V9)
- Upgrade Critic: construct explicit relativized worlds for each proof attempt
- Detect oracle-relative arguments, feed back to LLM Conjecturer
- Acceptance: one proof classified as relativizing with oracle witness; one non-relativizing variant proposed

### V5/V6/V7/V8: Publication + Bets B/C/D (Parallel after V9)

---

## Key File Index

| File | Role | Recent Changes |
|---|---|---|
| `search/circuits/synthesis.py` | CNF encoding | Added streaming mode, `_encode_streaming_parity`, `_encode_single_row_streaming` |
| `search/agents/miner.py` | SAT orchestration | Auto-selects encoding mode; added `_generate_truth_table` |
| `search/templates/bet_a_circuits.py` | Lean stubs + CNF specs | Threshold for empty truth table changed n>8 -> n>10 |
| `search/agents/planner.py` | Task generation | Respects explicit `step` param from config |
| `infra/config/bet_a_v3_extension.yaml` | V3 n=11-15 config | Created |
| `docs/brainlift/saturday-dev-checklist-v2.md` | Roadmap | Added V4b, V9, V10; updated priority order |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN2Proof.lean` | Verified theorem | LRAT: 382dd167... |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN3Proof.lean` | Verified theorem | LRAT: 46e4bd59... |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN4Proof.lean` | Verified theorem | LRAT: 53aa50fc... |

---

## Blockers

- **n=16-20 blocked**: needs V4b algebraic encoding
- **Novel exploration blocked**: needs V9 LLM Conjecturer
- **No current blockers for V4b implementation** — can start immediately
