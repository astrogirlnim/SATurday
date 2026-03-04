# Active Context: Current Work and Next Steps

## Last Updated: 2026-01-28 (Session 3)

## Recent Work (This Session)

### Storage Compression — COMPLETE

Added auto-compress-after-solve to `search/bin/run_kissat`:
- New `compress_file()` function: gzip-compresses any file over 1MB in-place
  - Replaces `foo.cnf` with `foo.cnf.gz`, `foo.lrat` with `foo.lrat.gz`
  - Uses `compresslevel=6` (good ratio, not painfully slow)
  - Logs original size, compressed size, and ratio
  - Deletes original only after successful compression
- Wired in after solver completes: LRAT compressed first, then CNF
- Artifact store paths updated to reflect `.gz` filenames (`copy_to_store=False` so no store changes needed)
- Threshold: 1MB — small files (n<=7) skip compression, large files (n>=11) always compress
- Expected ratios: CNF ~8-10x, LRAT ~5-8x (both are repetitive text)

Also reverted all V4b experiment code:
- `miner.py`: removed tiered n thresholds and ephemeral temp-file logic; restored clean two-tier (n<=10 explicit, n>10 streaming)
- `synthesis.py`: `_encode_algebraic_parity` still present but not called; routing restored to streaming
- Deleted `infra/config/bet_a_v4b_test.yaml` (test config)
- Cleaned leftover large LRATs (1.1GB + 471MB) from failed runs; proofs/ back to 28MB

Git commit: "Add auto-compression to run_kissat; revert V4b experiments" (b0a8d9d)

### V4b Status — DEFERRED

Attempted two approaches for algebraic n=16+ encoding:
1. Symbolic XOR-chain: unsound — returns SAT because it only constrains one symbolic input point, not all 2^n inputs
2. Ephemeral streaming: no improvement — 94M clauses for n=17 takes minutes to write even to /tmp

Conclusion: V4b requires a fundamentally different problem formulation (e.g., BDD-based, algebraic circuit complexity methods). Deferred. Compression handles storage; n=16-20 remains a solve-time problem, not a storage problem.

---

## Current State

### What Works

1. Full agent pipeline: Planner -> Conjecturer -> Miner -> Formalizer -> Critic
2. Multi-circuit synthesis: monotone, AC0, formula circuits
3. Multi-function templates: 7 templates (parity, majority, threshold-2, threshold-3)
4. Streaming encoding: handles parity n=11-15 without loading full truth table
5. SAT solving with LRAT proof extraction (Kissat, ARM64)
6. Auto-compression: CNF and LRAT files >1MB gzip-compressed after solving
7. Content-addressed artifact store (SHA256)
8. Verified proofs: 3 complete Lean theorems (n=2, n=3, n=4 monotone parity)
9. Lean infrastructure: circuit semantics, LRAT-Lean axiom, tactic library

### What's Missing (The Honest Gap)

1. **LLM Conjecturer** (V9) — R2 is template-only; the system explores a fixed search space
2. **n=16-20** — streaming produces 2GB+ CNFs; requires algebraic encoding not yet found
3. **Bets B, C, D** (V6, V7, V8) — not started
4. **Real barrier analysis** (V10) — R5 is heuristic tagging only
5. **Publication package** (V5) — not started

---

## Next Steps (Dependency Order)

### V9: LLM Conjecturer Activation — HIGHEST LEVERAGE, NO BLOCKERS
- V1 and V2 are done (verified results exist to ground prompts)
- Pull a local math/proof LLM via Ollama (e.g. deepseek-r1, mathstral)
- Replace template generation in ConjecturerAgent with LLM prompting
- Feed known lower bounds (n=2-4 verified) as context; ask LLM to propose tighter bounds or novel circuit classes
- Implement prompt-response caching
- Acceptance: one LLM-proposed conjecture survives Miner refutation + compiles in Lean

### V4b: Algebraic Parity Encoding — DEFERRED (research problem)
- True algebraic SAT encoding for universal circuit correctness is non-trivial
- Not a software engineering problem; needs circuit complexity insight
- Low priority until a concrete approach is identified

### V5/V6/V7/V8: Publication + Bets B/C/D — MEDIUM, parallel after V9

---

## Key File Index

| File | Role | Recent Changes |
|---|---|---|
| `search/bin/run_kissat` | Kissat wrapper | Added `compress_file()`, auto-compress after solve |
| `search/agents/miner.py` | SAT orchestration | Reverted to clean V4: n<=10 explicit, n>10 streaming |
| `search/circuits/synthesis.py` | CNF encoding | `_encode_algebraic_parity` present but not called |
| `search/templates/bet_a_circuits.py` | Lean stubs + CNF specs | Threshold n>10 for streaming |
| `search/agents/planner.py` | Task generation | Respects explicit `step` param |
| `infra/config/bet_a_v3_extension.yaml` | V3 n=11-15 config | Exists |
| `docs/brainlift/saturday-dev-checklist-v2.md` | Roadmap | V4 compression item checked |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN2Proof.lean` | Verified theorem | LRAT: 382dd167... |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN3Proof.lean` | Verified theorem | LRAT: 46e4bd59... |
| `theory/Conjectures/BetA/Proofs/MonotoneParityN4Proof.lean` | Verified theorem | LRAT: 53aa50fc... |

---

## Blockers

- **n=16-20**: algebraic encoding is a research problem, not just implementation
- **Novel exploration**: needs V9 LLM Conjecturer — this is the next item
- **No blockers for V9**: Ollama is installable locally, V1/V2 results exist as grounding
