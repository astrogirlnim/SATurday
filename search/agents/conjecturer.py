"""
Conjecturer Agent - Template-based and LLM-driven conjecture generation.

This agent generates conjectures using:
- Grammar-driven templates (Bet A circuits, Bet B algorithms)
- Optional local LLM via Ollama (V9: deepseek-r1 or compatible model)

LLM path: when config has agents.conjecturer.llm.enabled = true,
the agent calls the local Ollama endpoint to generate Lean stubs and
CNF specs from a structured prompt. Results are cached to avoid redundant
calls. Falls back to template path on any LLM error.

Outputs:
- Lean theorem stubs written to theory/Conjectures/
- CNF specifications written to search/specs/
"""

from typing import Any, Dict, List, Optional
from pathlib import Path
import json
import hashlib
import time
from .core import AgentBase, AgentContext, AgentResult

# Import template system
import sys
sys.path.insert(0, str(Path(__file__).parent.parent))

from templates.base import TemplateRegistry, Conjecture
from templates.bet_a_circuits import (
    MonotoneParityTemplate,
    MonotoneMajorityTemplate,
    MonotoneThresholdTemplate,
    AC0ParityTemplate,
    AC0MajorityTemplate,
    FormulaParityTemplate,
)
from templates.bet_b_algorithms import (
    SortingAlgorithmTemplate,
    SearchingAlgorithmTemplate,
    GraphReachabilityTemplate,
)
# V7: Bet C hardness-vs-randomness templates
from templates.bet_c_hardness import (
    HardnessCorrelationTemplate,
    PRGSecurityTemplate,
    NisanWigdersonImplicationTemplate,
)
# V8: Bet D barrier-aware reduction templates
from templates.bet_d_barriers import (
    NonRelativizingReductionTemplate,
    OracleBarrierTestTemplate,
    AlgebraizationReductionTemplate,
)


class ConjecturerAgent(AgentBase):
    """
    Template-based and LLM-driven conjecture generator.

    Generates conjectures from planner tasks using:
    1. Template path (default): bet-specific templates for Bet A and Bet B.
    2. LLM path (optional): local Ollama model generates Lean stubs and CNF
       specs from structured prompts. Activated when config has
       agents.conjecturer.llm.enabled = true.

    For each task:
    - Selects appropriate template OR calls LLM endpoint
    - Generates Lean theorem stub with sorry placeholder
    - Generates CNF specification for SAT mining
    - Writes both to output directories
    - Caches LLM responses to avoid duplicate API calls
    """

    def __init__(self):
        super().__init__("conjecturer")
        self.registry = TemplateRegistry()
        self._register_templates()
        # LLM prompt cache: keyed by SHA256(prompt), value is LLM response text
        self._llm_cache: Dict[str, str] = {}
        print(f"[ConjecturerAgent] Initialized with {len(self.registry.get_all_templates())} template types")
    
    def _register_templates(self):
        """Register all available templates for Bet A (circuits) and Bet B (algorithms)."""
        print("[ConjecturerAgent] Registering templates...")

        # Bet A: Circuit lower bounds
        self.registry.register("A", "monotone", "parity",      MonotoneParityTemplate())
        self.registry.register("A", "monotone", "majority",    MonotoneMajorityTemplate())
        self.registry.register("A", "monotone", "threshold_2", MonotoneThresholdTemplate(threshold_k=2))
        self.registry.register("A", "monotone", "threshold_3", MonotoneThresholdTemplate(threshold_k=3))
        self.registry.register("A", "ac0",      "parity",      AC0ParityTemplate())
        self.registry.register("A", "ac0",      "majority",    AC0MajorityTemplate())
        self.registry.register("A", "formula",  "parity",      FormulaParityTemplate())

        # Bet B: Algorithm synthesis
        # Key: (bet="B", circuit_type=schema_name, function_name="algorithm")
        self.registry.register("B", "sorting",    "algorithm", SortingAlgorithmTemplate())
        self.registry.register("B", "searching",  "algorithm", SearchingAlgorithmTemplate())
        self.registry.register("B", "graph_reach","algorithm", GraphReachabilityTemplate())

        # V7: Bet C: Hardness-vs-Randomness
        # Key: (bet="C", circuit_type=circuit_type, function_name=schema_name)
        # Schema name is stored in algorithm_schema field and used as the key's circuit_type.
        # For each (circuit_type, function) pair we register the three schema variants.
        # Registration covers: (C, hardness_correlation, parity), (C, prg_security, parity), etc.
        # The conjecturer routes via algorithm_schema -> circuit_type for Bet C (same as Bet B).
        for c_type in ["monotone", "ac0"]:
            self.registry.register("C", "hardness_correlation", "parity",
                                   HardnessCorrelationTemplate())
            self.registry.register("C", "prg_security",         "parity",
                                   PRGSecurityTemplate())
            self.registry.register("C", "nw_implication",       "parity",
                                   NisanWigdersonImplicationTemplate())

        # V8: Bet D: Barrier-Aware Reductions
        # Key: (bet="D", algorithm_schema=schema_name, function_name=source_problem)
        # algorithm_schema carries the reduction schema; function_name carries the source problem.
        # Registered for each source problem variant (sat, 3sat, circuit_sat).
        for src in ["sat", "3sat", "circuit_sat"]:
            self.registry.register("D", "non_relativizing_reduction", src,
                                   NonRelativizingReductionTemplate())
            self.registry.register("D", "oracle_barrier_test",        src,
                                   OracleBarrierTestTemplate())
            self.registry.register("D", "algebraization_reduction",   src,
                                   AlgebraizationReductionTemplate())

        print(f"[ConjecturerAgent] Registered {len(self.registry.get_all_templates())} templates")
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Plan conjecture generation based on tasks from planner.
        
        Phase 1: Planning
        - Extract tasks from planner artifacts
        - Count tasks by bet and circuit type
        - Determine output directories
        - Select sampling strategy (for large task lists)
        """
        context.log(self.name, "=== PHASE 1: PLANNING ===")
        context.log(self.name, "Planning conjecture generation")
        
        # Get plan from planner artifacts
        planner_artifacts = context.artifacts.get("planner", {})
        planner_plan = planner_artifacts.get("plan", {})
        tasks = planner_plan.get("tasks", [])
        
        context.log(self.name, f"Received {len(tasks)} tasks from planner")
        
        # Analyze task distribution
        task_by_bet = {}
        task_by_circuit = {}
        for task in tasks:
            bet = task.get("bet", "unknown")
            circuit_type = task.get("circuit_type", "unknown")
            
            task_by_bet[bet] = task_by_bet.get(bet, 0) + 1
            task_by_circuit[circuit_type] = task_by_circuit.get(circuit_type, 0) + 1
        
        context.log(self.name, f"Tasks by bet: {task_by_bet}")
        context.log(self.name, f"Tasks by circuit type: {task_by_circuit}")
        
        # For MVP: Limit number of conjectures to avoid overwhelming output
        # Check in agents.conjecturer first, then fall back to top-level config
        agents_config = context.config.get("agents", {})
        conjecturer_config = agents_config.get("conjecturer", {})
        max_conjectures = conjecturer_config.get("max_conjectures", context.config.get("max_conjectures", 10))
        sample_tasks = tasks[:max_conjectures] if len(tasks) > max_conjectures else tasks
        
        if len(tasks) > max_conjectures:
            context.log(
                self.name,
                f"Sampling {max_conjectures} tasks from {len(tasks)} (MVP limit)",
                level="INFO"
            )
        
        # Determine output directories
        repo_root = Path(__file__).parent.parent.parent
        lean_dir = repo_root / "theory" / "Conjectures"
        spec_dir = repo_root / "search" / "specs"
        
        generation_plan = {
            "tasks": sample_tasks,
            "num_tasks": len(sample_tasks),
            "mode": "template",
            "output_dirs": {
                "lean": str(lean_dir),
                "specs": str(spec_dir),
            },
        }
        
        context.log(self.name, f"Will generate {len(sample_tasks)} conjectures")
        context.log(self.name, f"Lean stubs: {lean_dir}")
        context.log(self.name, f"CNF specs: {spec_dir}")
        
        return generation_plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Generate conjectures using templates.
        
        Phase 2: Acting
        - For each task, select appropriate template
        - Instantiate template with task parameters
        - Generate Lean stub and CNF spec
        - Write to output directories
        - Track successes and failures
        """
        context.log(self.name, "=== PHASE 2: ACTING ===")
        context.log(self.name, "Generating conjectures from templates")
        
        tasks = plan["tasks"]
        registry = self.registry  # Use agent's registry instead of passing through plan
        lean_dir = Path(plan["output_dirs"]["lean"])
        spec_dir = Path(plan["output_dirs"]["specs"])
        
        context.log(self.name, f"Processing {len(tasks)} tasks")
        
        # Generate conjectures
        conjectures: List[Conjecture] = []
        failed_tasks = []
        
        # Determine LLM config
        agents_config = context.config.get("agents", {})
        conjecturer_config = agents_config.get("conjecturer", {})
        llm_config = conjecturer_config.get("llm", {})
        llm_enabled = llm_config.get("enabled", False)
        llm_model   = llm_config.get("model", "deepseek-r1:7b")
        llm_endpoint = llm_config.get("endpoint", "http://localhost:11434")

        if llm_enabled:
            context.log(self.name, f"LLM mode enabled: model={llm_model}, endpoint={llm_endpoint}")
        else:
            context.log(self.name, "LLM mode disabled: using template path only")

        for i, task in enumerate(tasks):
            task_id = task.get("task_id", f"task_{i}")
            bet = task.get("bet", "A")
            # Bet B, C, D all use algorithm_schema as the lookup key's "circuit_type".
            # Bet D additionally uses function_name (source_problem) as the registry key.
            algorithm_schema = task.get("algorithm_schema")
            if bet == "B":
                # Bet B: algorithm_schema is the schema (sorting/searching/graph_reach)
                circuit_type = algorithm_schema if algorithm_schema else task.get("circuit_type", "unknown")
            elif bet == "C":
                # V7: Bet C: algorithm_schema is the test schema (hardness_correlation/prg_security/nw_implication)
                circuit_type = algorithm_schema if algorithm_schema else task.get("circuit_type", "unknown")
            elif bet == "D":
                # V8: Bet D: algorithm_schema is the reduction schema
                # (non_relativizing_reduction/oracle_barrier_test/algebraization_reduction)
                circuit_type = algorithm_schema if algorithm_schema else task.get("circuit_type", "unknown")
            else:
                circuit_type = task.get("circuit_type", "unknown")

            # Determine function_name for registry lookup
            if bet == "B":
                function_name = "algorithm"
            elif bet == "D":
                # V8: function_name is the source problem (sat/3sat/circuit_sat)
                function_name = task.get("function_name", "sat")
            else:
                function_name = task.get("function_name", "parity")

            context.log(self.name, f"Processing task {i+1}/{len(tasks)}: {task_id} (bet={bet}, type={circuit_type})")

            try:
                conjecture: Optional[Conjecture] = None

                # LLM path: attempt first if enabled
                if llm_enabled:
                    conjecture = self._generate_via_llm(
                        context, task, llm_endpoint, llm_model,
                        lean_dir, spec_dir
                    )
                    if conjecture:
                        context.log(self.name, f"LLM generated conjecture for {task_id}")
                    else:
                        context.log(self.name, f"LLM failed for {task_id}, falling back to template", level="WARNING")

                # Template path: fallback (or primary if LLM disabled)
                if conjecture is None:
                    template = registry.get_template(bet, circuit_type, function_name)

                    if not template:
                        context.log(
                            self.name,
                            f"No template for (bet={bet}, type={circuit_type}, function={function_name})",
                            level="WARNING"
                        )
                        failed_tasks.append(task_id)
                        continue

                    context.log(self.name, f"Using template: {template.template_id}")
                    conjecture = template.instantiate(task)

                # Write Lean stub
                lean_path = conjecture.write_lean_stub(lean_dir)
                context.log(self.name, f"Wrote Lean stub: {lean_path}")

                # Write CNF spec
                spec_path = conjecture.write_cnf_spec(spec_dir)
                context.log(self.name, f"Wrote CNF spec: {spec_path}")

                conjectures.append(conjecture)

            except Exception as e:
                context.log(
                    self.name,
                    f"Failed to generate conjecture for {task_id}: {e}",
                    level="ERROR"
                )
                failed_tasks.append(task_id)
        
        context.log(
            self.name,
            f"Generated {len(conjectures)} conjectures ({len(failed_tasks)} failed)"
        )

        # Store conjectures in artifacts
        artifacts = {
            "conjectures": [c.to_dict() for c in conjectures],
            "failed_tasks": failed_tasks,
            "lean_dir": str(lean_dir),
            "spec_dir": str(spec_dir),
        }
        
        metrics = {
            "num_generated": len(conjectures),
            "num_failed": len(failed_tasks),
            "success_rate": len(conjectures) / len(tasks) if tasks else 0,
            "mode": "llm+template" if llm_enabled else "template",
            "llm_enabled": llm_enabled,
        }
        
        status = "success" if conjectures else "failure"
        
        return AgentResult(
            agent_name=self.name,
            status=status,
            artifacts=artifacts,
            metrics=metrics,
        )

    # ------------------------------------------------------------------
    # LLM Conjecture Generation (V9)
    # ------------------------------------------------------------------

    def _generate_via_llm(
        self,
        context: AgentContext,
        task: Dict[str, Any],
        endpoint: str,
        model: str,
        lean_dir: Path,
        spec_dir: Path,
    ) -> Optional[Conjecture]:
        """
        Generate a conjecture using a local Ollama LLM.

        Sends a structured prompt describing the research task and asks the
        model to produce:
        1. A Lean 4 theorem stub (with sorry placeholder)
        2. A YAML CNF spec dictionary

        The response is parsed and a Conjecture object is constructed.
        Results are cached by prompt hash to avoid duplicate calls.

        Args:
            context:   Agent execution context (for logging)
            task:      Task dictionary from planner
            endpoint:  Ollama base URL (e.g., http://localhost:11434)
            model:     Ollama model name (e.g., deepseek-r1:7b)
            lean_dir:  Output directory for Lean stubs
            spec_dir:  Output directory for CNF specs

        Returns:
            Conjecture on success, None on any failure (triggers fallback)
        """
        try:
            import urllib.request
            import urllib.error

            task_id      = task.get("task_id", "unknown")
            bet          = task.get("bet", "A")
            n            = task.get("problem_size", 2)
            seed         = task.get("seed", 0)
            circuit_type = task.get("circuit_type") or task.get("algorithm_schema", "unknown")
            func_name    = task.get("function_name") or task.get("algorithm_schema", "unknown")

            # Build prompt
            prompt = self._build_llm_prompt(task_id, bet, n, seed, circuit_type, func_name)

            # Check cache first
            prompt_hash = hashlib.sha256(prompt.encode()).hexdigest()[:16]
            if prompt_hash in self._llm_cache:
                context.log(self.name, f"LLM cache hit for task {task_id} (hash={prompt_hash})")
                raw_response = self._llm_cache[prompt_hash]
            else:
                context.log(self.name, f"Calling Ollama model={model} for task {task_id}")
                raw_response = self._call_ollama(endpoint, model, prompt)
                self._llm_cache[prompt_hash] = raw_response
                context.log(self.name, f"LLM response cached (hash={prompt_hash})")

            # Parse LLM response into Conjecture fields
            lean_stub, cnf_spec = self._parse_llm_response(raw_response, task_id, bet, n, seed)

            if lean_stub is None or cnf_spec is None:
                context.log(self.name, f"LLM response parse failed for {task_id}", level="WARNING")
                return None

            conjecture_id = f"llm_{bet.lower()}_{circuit_type}_n{n}_s{seed}"

            conjecture = Conjecture(
                conjecture_id=conjecture_id,
                task_id=task_id,
                bet=bet,
                lean_stub=lean_stub,
                cnf_spec=cnf_spec,
                metadata={
                    "template_id": f"llm_{model}",
                    "problem_size": n,
                    "seed": seed,
                    "circuit_type": circuit_type,
                    "llm_model": model,
                    "prompt_hash": prompt_hash,
                },
            )

            context.log(self.name, f"LLM conjecture created: {conjecture_id}")
            return conjecture

        except Exception as e:
            context.log(self.name, f"LLM generation error for task {task.get('task_id')}: {e}", level="ERROR")
            return None

    def _build_llm_prompt(
        self,
        task_id: str,
        bet: str,
        n: int,
        seed: int,
        circuit_type: str,
        func_name: str,
    ) -> str:
        """
        Build a structured prompt for the LLM.

        The prompt explicitly:
        - Describes the research context (circuit complexity / algorithm synthesis)
        - Specifies the theorem to be conjectured
        - Requests Lean 4 stub in a clearly delimited block
        - Requests CNF spec as YAML in a clearly delimited block
        - Instructs the model never to use hyphens in output

        Args:
            task_id, bet, n, seed, circuit_type, func_name: Task parameters

        Returns:
            Prompt string
        """
        if bet == "A":
            problem_desc = (
                f"circuit lower bound: does a {circuit_type} circuit of size <= {n*n} "
                f"compute the {func_name} function on {n} inputs?"
            )
            lean_context = (
                f"The theorem should state: any {circuit_type} circuit computing "
                f"{func_name} on {n} inputs requires more than {n} gates."
            )
        else:
            problem_desc = (
                f"algorithm synthesis: does a {circuit_type} algorithm schema of "
                f"at most {n*n} steps correctly solve the {func_name} problem on inputs of size {n}?"
            )
            lean_context = (
                f"The theorem should state existence of a program schema of depth <= {n*n} "
                f"that correctly solves {func_name} for all inputs of size {n}."
            )

        # Few-shot example to anchor the output format.
        # The model must copy this pattern exactly, substituting the given values.
        few_shot_example = f"""<LEAN_STUB>
import Mathlib.Tactic

theorem example_lower_bound : True := by
  sorry
</LEAN_STUB>

<CNF_SPEC>
conjecture_id: example_n2_s0
task_id: example_task
description: example problem n=2
circuit:
  type: monotone
  num_inputs: 2
  max_gates: 4
target_function:
  name: parity
  n: 2
encoding:
  method: circuit_synthesis
seed: 0
solver_config:
  timeout_seconds: 60
</CNF_SPEC>"""

        prompt = f"""Output exactly two tagged blocks. No explanation. No extra text.

Example format:
{few_shot_example}

Now generate a similar pair for:
{lean_context}
Do not use hyphens. Use sorry as the Lean proof body.
task_id={task_id}, bet={bet}, n={n}, seed={seed}
circuit_type={circuit_type}, function={func_name}
conjecture_id={task_id.replace('bet_', 'llm_')}"""

        return prompt

    def _call_ollama(self, endpoint: str, model: str, prompt: str) -> str:
        """
        Call Ollama REST API to generate a completion.

        Uses /api/generate endpoint with stream=false.

        Args:
            endpoint: Ollama base URL
            model:    Model name
            prompt:   Input prompt

        Returns:
            Response text from the model

        Raises:
            Exception on network or HTTP error
        """
        import urllib.request
        import urllib.error

        url = f"{endpoint}/api/generate"
        payload = json.dumps({
            "model": model,
            "prompt": prompt,
            "stream": False,
            "options": {
                "temperature": 0.2,
                # 4096 tokens: enough for thinking + structured output blocks.
                # DeepSeek-R1 models emit chain-of-thought in "thinking" before "response".
                "num_predict": 4096,
            },
        }).encode("utf-8")

        print(f"[ConjecturerAgent] POST {url} model={model}")
        start_time = time.time()

        req = urllib.request.Request(
            url,
            data=payload,
            headers={"Content-Type": "application/json"},
            method="POST",
        )

        with urllib.request.urlopen(req, timeout=120) as resp:
            raw = resp.read().decode("utf-8")

        elapsed = time.time() - start_time
        print(f"[ConjecturerAgent] Ollama response received in {elapsed:.1f}s ({len(raw)} bytes)")

        data = json.loads(raw)

        # DeepSeek-R1 models output chain-of-thought in "thinking" and the final answer
        # in "response". If "response" is empty, fall back to "thinking" content.
        response_text = data.get("response", "")
        thinking_text = data.get("thinking", "")
        done_reason   = data.get("done_reason", "unknown")

        print(f"[ConjecturerAgent] done_reason={done_reason}, response={len(response_text)} chars, thinking={len(thinking_text)} chars")

        if not response_text and thinking_text:
            # Model used all tokens in thinking; extract structured blocks from thinking
            print(f"[ConjecturerAgent] Response empty, using thinking field ({len(thinking_text)} chars)")
            response_text = thinking_text

        print(f"[ConjecturerAgent] LLM effective response length: {len(response_text)} chars")
        return response_text

    # ------------------------------------------------------------------
    # V10: Non-Relativizing Tweak Proposal (Oracle Feedback Loop)
    # ------------------------------------------------------------------

    def propose_non_relativizing_tweak(
        self,
        oracle_witness: Dict[str, Any],
        context: "AgentContext",
        endpoint: str,
        model: str,
    ) -> Optional[str]:
        """
        V10: Given an oracle witness from the Critic, ask the LLM to propose
        a non-relativizing variant of the proof technique.

        This closes the loop: Critic detects relativization -> oracle witness ->
        Conjecturer proposes a fix -> Critic re-evaluates.

        The prompt describes the oracle world and asks for a concrete
        non-relativizing Lean proof sketch to replace the current approach.

        Args:
            oracle_witness: Dict from OracleWitness.to_dict()
            context:        Agent context for logging
            endpoint:       Ollama base URL
            model:          Ollama model name

        Returns:
            Non-relativizing proof sketch as a string, or None on failure
        """
        print(f"[ConjecturerAgent] V10: Proposing non-relativizing tweak for oracle witness")
        print(f"[ConjecturerAgent] V10: Oracle type={oracle_witness.get('oracle_type')}, "
              f"technique={oracle_witness.get('proof_technique')}")

        if not oracle_witness.get("relativizes", True):
            print(f"[ConjecturerAgent] V10: Witness is non-relativizing; no tweak needed")
            return None

        circuit_class   = oracle_witness.get("circuit_class", "monotone")
        technique       = oracle_witness.get("proof_technique", "unknown")
        oracle_desc     = oracle_witness.get("witness_description", "")[:200]
        oracle_queries  = oracle_witness.get("oracle_queries", [])
        existing_suggest = oracle_witness.get("non_rel_suggestion", "")

        # Build prompt for non-relativizing alternative
        query_text = "\n".join(f"  {q[:100]}" for q in oracle_queries[:2]) if oracle_queries else "  (none)"

        prompt = f"""You are a complexity theorist helping to fix a relativizing proof.

The proof for a {circuit_class} circuit lower bound uses technique: {technique}
This technique relativizes, meaning it cannot separate P from NP.

Oracle witness:
{oracle_desc}

Oracle queries that break the argument:
{query_text}

Existing suggestion: {existing_suggest[:200] if existing_suggest else "none"}

Task: Propose a concrete non-relativizing Lean 4 proof sketch that could replace
or augment the current technique. Focus on algebraic or arithmetization-based arguments.

Respond in this format (no hyphens):

<NON_REL_SKETCH>
[Lean 4 proof sketch using non-relativizing techniques. 
Must use algebraic or polynomial methods, not case analysis or simple induction.
Include: theorem statement, key lemmas, and a brief proof strategy.]
</NON_REL_SKETCH>"""

        try:
            response = self._call_ollama(endpoint, model, prompt)
            if not response:
                return None

            import re
            match = re.search(r"<NON_REL_SKETCH>(.*?)</NON_REL_SKETCH>", response, re.DOTALL)
            if match:
                sketch = match.group(1).strip()
                print(f"[ConjecturerAgent] V10: Non-rel sketch generated ({len(sketch)} chars)")
                if context:
                    context.log("conjecturer", f"V10: Non-rel tweak proposed ({len(sketch)} chars)")
                return sketch
            else:
                print(f"[ConjecturerAgent] V10: No <NON_REL_SKETCH> block in LLM response")
                return None

        except Exception as e:
            print(f"[ConjecturerAgent] V10: Non-rel tweak generation failed: {e}", file=__import__("sys").stderr)
            return None

    def _parse_llm_response(
        self,
        raw: str,
        task_id: str,
        bet: str,
        n: int,
        seed: int,
    ):
        """
        Parse LLM response into (lean_stub, cnf_spec) tuple.

        Expects delimited blocks:
          <LEAN_STUB>...</LEAN_STUB>
          <CNF_SPEC>...</CNF_SPEC>

        Args:
            raw:     Raw LLM response text
            task_id: Task ID for logging
            bet, n, seed: Fallback values if parsing fails

        Returns:
            (lean_stub: str | None, cnf_spec: dict | None)
        """
        import re
        import yaml as _yaml

        lean_stub = None
        cnf_spec  = None

        # Extract Lean stub
        lean_match = re.search(r"<LEAN_STUB>(.*?)</LEAN_STUB>", raw, re.DOTALL)
        if lean_match:
            lean_stub = lean_match.group(1).strip()
            print(f"[ConjecturerAgent] Parsed Lean stub ({len(lean_stub)} chars)")
        else:
            print(f"[ConjecturerAgent] No <LEAN_STUB> block found in LLM response for {task_id}")

        # Extract CNF spec YAML
        spec_match = re.search(r"<CNF_SPEC>(.*?)</CNF_SPEC>", raw, re.DOTALL)
        if spec_match:
            yaml_text = spec_match.group(1).strip()
            try:
                cnf_spec = _yaml.safe_load(yaml_text)
                if not isinstance(cnf_spec, dict):
                    print(f"[ConjecturerAgent] CNF spec is not a dict for {task_id}")
                    cnf_spec = None
                else:
                    # Ensure required fields are present
                    cnf_spec.setdefault("conjecture_id", f"llm_{bet.lower()}_n{n}_s{seed}")
                    cnf_spec.setdefault("task_id", task_id)
                    cnf_spec.setdefault("seed", seed)
                    print(f"[ConjecturerAgent] Parsed CNF spec: {list(cnf_spec.keys())}")
            except Exception as e:
                print(f"[ConjecturerAgent] YAML parse error for {task_id}: {e}")
                cnf_spec = None
        else:
            print(f"[ConjecturerAgent] No <CNF_SPEC> block found in LLM response for {task_id}")

        return lean_stub, cnf_spec

    def report(self, context: AgentContext, result: AgentResult) -> str:
        """
        Generate Markdown report for conjecture generation.
        
        Phase 3: Reporting
        - Summary statistics
        - List of generated conjectures
        - File locations
        - Failures (if any)
        """
        context.log(self.name, "=== PHASE 3: REPORTING ===")
        context.log(self.name, "Generating conjecture report")
        
        conjectures = result.artifacts.get("conjectures", [])
        failed_tasks = result.artifacts.get("failed_tasks", [])
        num_generated = result.metrics.get("num_generated", 0)
        num_failed = result.metrics.get("num_failed", 0)
        success_rate = result.metrics.get("success_rate", 0)
        
        lean_dir = result.artifacts.get("lean_dir", "unknown")
        spec_dir = result.artifacts.get("spec_dir", "unknown")
        
        # Build report
        report = f"""# Conjecturer Agent Report

## Summary
- Conjectures Generated: **{num_generated}**
- Failed Tasks: **{num_failed}**
- Success Rate: **{success_rate:.1%}**
- Mode: **Template-based**
- Status: **{result.status}**

## Output Directories

- Lean stubs: `{lean_dir}`
- CNF specifications: `{spec_dir}`

## Generated Conjectures

"""
        
        # Group conjectures by template type
        by_template = {}
        for conj in conjectures:
            template_id = conj.get("metadata", {}).get("template_id", "unknown")
            if template_id not in by_template:
                by_template[template_id] = []
            by_template[template_id].append(conj)
        
        for template_id, template_conjs in sorted(by_template.items()):
            report += f"\n### {template_id} ({len(template_conjs)} conjectures)\n\n"
            
            for conj in template_conjs[:5]:  # Show first 5 per template
                conj_id = conj.get("conjecture_id", "unknown")
                task_id = conj.get("task_id", "unknown")
                lean_file = conj.get("lean_file", "unknown")
                spec_file = conj.get("spec_file", "unknown")
                
                report += f"- **{conj_id}**\n"
                report += f"  - Task: `{task_id}`\n"
                report += f"  - Lean: `{lean_file}`\n"
                report += f"  - Spec: `{spec_file}`\n"
            
            if len(template_conjs) > 5:
                report += f"  - ... and {len(template_conjs) - 5} more\n"
        
        if failed_tasks:
            report += "\n## Failed Tasks\n\n"
            for task_id in failed_tasks[:10]:
                report += f"- {task_id}\n"
            if len(failed_tasks) > 10:
                report += f"- ... and {len(failed_tasks) - 10} more\n"
        
        report += "\n## Next Steps\n\n"
        report += "1. **Miner Agent** will process CNF specifications\n"
        report += "   - Run Kissat on generated specs\n"
        report += "   - Extract counterexamples or confidence patterns\n"
        report += "   - Generate LRAT proofs for UNSAT results\n\n"
        report += "2. **Formalizer Agent** will process Lean stubs\n"
        report += "   - Attempt to fill in sorry placeholders\n"
        report += "   - Apply tactic libraries\n"
        report += "   - Verify proofs compile\n\n"
        report += "3. **Critic Agent** will analyze completed proofs\n"
        report += "   - Check for barrier violations\n"
        report += "   - Suggest improvements\n"
        
        context.log(self.name, "Report generation complete")
        
        return report

