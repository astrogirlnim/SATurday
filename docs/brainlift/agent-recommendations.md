In the **SATurday** project, the five agents (**Planner**, **Conjecturer**, **Counterexample Miner**, **Formalizer**, and **Proof Critic**) form a custom, lightweight multi-agent research loop tailored to exploring P vs NP bets locally on your M4 MacBook.

None of them come as fully off-the-shelf, plug-and-play components that exactly match your specialized needs (especially the barrier-aware aspects and tight integration with Kissat SAT solving + Lean 4 formalization). Instead, you'll **build them yourself** in Python (mostly in `search/agents/`) as modular classes inheriting from a shared `AgentBase` interface, following the MVP checklist (F6 supervisor skeleton + Phase 3/4 implementations).

That said, you can (and should) **heavily draw inspiration, code patterns, and even reusable components** from the vibrant open-source ecosystem around **Lean 4 theorem-proving agents** and **LLM-assisted formal math** (as of January 2026). Many projects provide excellent starting points for tactic suggestion, proof search, error feedback, retrieval, and multi-agent orchestration — especially since your **Conjecturer** and **Formalizer** agents are LLM/tactic-heavy, and the **Proof Critic** needs reasoning over proof structure.

### Where to Source Inspiration/Code for Each Agent

Here's a breakdown per agent, with the most relevant open-source projects (all GitHub-accessible, local-runnable on M4 with proper setup like MLX/Ollama for small models or CPU inference):

- **Planner** (rule-based task decomposition, budget/time enforcement, YAML plans)
  - **Build mostly from scratch** (simple rule engine + YAML loader in Python).
  - Inspiration: Multi-agent orchestrators like those in **Ax-Prover** (multi-agent workflow with Orchestrator agent for planning/proof decomposition) or general agent frameworks (e.g., patterns from **MA-LoT** paper's multi-agent Lean setup, though code may not be fully released yet).
  - **LeanCopilot** and **LeanAgent** show how to structure sequential/iterative agent calls in Lean environments.

- **Conjecturer** (LLM-assisted or template-based lemma/reduction proposal, emits Lean stubs + CNF specs)
  - **Primary sources**:
    - **LeanCopilot** (GitHub: lean-dojo/LeanCopilot) — Excellent for integrating LLMs directly as copilots in Lean: suggests tactics/premises, supports local models (via llama.cpp, MLX, etc.), and can generate conjecture-like stubs. You can adapt its inference pipeline for your template/LLM hybrid mode (R2).
    - **ReProver** (GitHub: lean-dojo/ReProver) — Retrieval-augmented prover from LeanDojo; embeds states/premises and generates tactics. Great for premise suggestion → conjecture drafting. Runs locally, ByT5-based encoder is lightweight for M4.
    - **DeepSeek-Prover-V2** (Hugging Face: deepseek-ai/DeepSeek-Prover-V2-7B or larger) — Open-source LLM specifically trained for Lean 4 proof generation. Download and run locally (7B version fits on M4 with quantization/MLX). Use it to generate micro-lemmas/conjectures.
  - Bonus: **COPRA** (in-context agent with error feedback/backtracking) — patterns for iterative conjecture refinement.

- **Counterexample Miner** (PySAT/Kissat-based CNF search, pattern extraction from DRAT/LRAT logs)
  - **Build custom** (your Kissat wrapper + stats extraction is unique).
  - Inspiration: Any SAT tooling repos (e.g., patterns from PySAT examples or solver trace parsers in SAT competition tools), but no direct agentic equivalent — this is your project's novel piece.

- **Formalizer** (Lean 4 proof steps, tactic library, convert templates to theorems)
  - **Primary sources**:
    - **LeanCopilot** again — Native Lean integration for tactic suggestion and proof completion.
    - **Aesop** (GitHub: leanprover-community/aesop) — White-box automation tactic for Lean 4 (like Isabelle's auto); extendable for your routine induction/encoding scaffolds.
    - **LeanAgent** (GitHub: lean-dojo/LeanAgent) — Lifelong learning framework for theorem proving; shows how to structure progressive proof building without forgetting.
    - General tactic libraries in Mathlib4 (leanprover-community/mathlib4) — borrow induction/circuit lemmas.

- **Proof Critic** (barrier-aware: detect relativizing/natural-proof patterns, oracle diagnostics)
  - **Build custom** (heuristic/static analysis + oracle checks are research-specific).
  - Inspiration: Proof analysis/repair agents like **APOLLO** (GitHub: aziksh-ospanov/APOLLO) — modular LLM + Lean repair loop that analyzes errors, fixes syntax, isolates subgoals — adapt for barrier tagging.
    - **Ax-Prover** (described in arXiv 2510.12787; uses lean-lsp-mcp for tool calls) — Verifier agent checks proofs rigorously; multi-agent setup with Prover/Verifier/Orchestrator. Code may be partially available via lean-lsp-mcp repo patterns.

### Practical Recommendations for Your MVP

- **Start simple**: Implement agents as pure Python classes first (templates/rules only, no LLM). Get the loop running end-to-end on tiny instances (Phase 3 MVP).
- **Add LLM power incrementally** (R12 optional): Use **MLX** (Apple Silicon optimized) + **DeepSeek-Prover-V2-7B** (quantized) or **LeanCopilot**'s local inference for Conjecturer/Formalizer. Both run offline on M4 with 16GB+ RAM.
- **Best starting repos to fork/integrate patterns from**:
  - lean-dojo/LeanCopilot → LLM integration in Lean
  - lean-dojo/ReProver → Retrieval + tactic generation
  - lean-dojo/LeanAgent → Lifelong/progressive proving
  - aziksh-ospanov/APOLLO → Proof repair/analysis loop

The ecosystem is moving fast in 2026 — check the Lean Zulip (leanprover.zulipchat.com) for the latest on these projects, and watch for releases from DeepSeek, LeanDojo team, etc. By building on these, you'll avoid reinventing LLM-Lean bridging while keeping SATurday focused on your unique P vs NP + SAT verification angle.

This approach keeps the project zero-cost, local, and reproducible while leveraging the best open-source building blocks available today! 