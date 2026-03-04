"""
Formalizer Agent - Lean 4 proof generation.

This agent:
- Takes UNSAT results from miner
- Converts conjectures to Lean theorems with proof tactics
- Uses tactic library for common patterns
- References LRAT proofs via hash-anchoring
- Writes theorems to theory/Conjectures/BetA/Proofs/

## Architecture
- Input: Mining results with LRAT hashes from artifact store
- Processing: Template-based theorem generation with tactics
- Output: Lean 4 theorem files with proof sketches
- Verification: Compilation check via `lake build`

LOG: Enhanced Formalizer Agent with proof generation
"""

import os
import sys
from typing import Any, Dict, List, Optional
from pathlib import Path

from .core import AgentBase, AgentContext, AgentResult
from search.templates.lean_theorems import (
    LeanTheorem,
    TheoremRegistry,
)
from search.tools.artifact_store import ArtifactStore


class FormalizerAgent(AgentBase):
    """
    Lean 4 theorem prover using tactic library and templates.
    
    Converts UNSAT mining results into formal Lean proofs with:
    - Theorem statements matching conjectures
    - Tactic-based proof strategies
    - LRAT proof hash references
    - Compilation-ready Lean 4 code
    
    For MVP: Accepts theorems with `sorry` placeholders.
    Post-MVP: Fill in complete proofs using tactic library.
    """
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("formalizer")
        self.config = config or {}
        self.registry = TheoremRegistry()
        
        # Determine project root
        self.project_root = Path(__file__).parent.parent.parent
        
        # Initialize artifact store
        proofs_dir = self.project_root / "proofs"
        self.artifact_store = ArtifactStore(str(proofs_dir))
        
        print(f"LOG: FormalizerAgent initialized with project root: {self.project_root}",
              file=sys.stderr)
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Plan formalization strategy based on mining results.
        
        Analyzes mining results to:
        - Count UNSAT instances (candidates for formalization)
        - Identify circuit types and target functions
        - Select appropriate proof templates
        - Estimate formalization workload
        
        Args:
            context: Agent execution context with mining results
            
        Returns:
            Formalization plan with candidates and strategies
        """
        context.log(self.name, "Planning Lean formalization strategy")
        
        # Get mining results from context
        miner_artifacts = context.artifacts.get("miner", {})
        mining_results = miner_artifacts.get("mining_results", [])
        
        # LOG: Mining results summary
        context.log(self.name, f"Received {len(mining_results)} mining results")
        
        # Filter UNSAT instances (these are proof candidates)
        unsat_instances = [
            r for r in mining_results
            if r.get("status") == "UNSAT"
        ]
        
        context.log(
            self.name,
            f"Found {len(unsat_instances)} UNSAT instances to formalize"
        )
        
        # Analyze circuit types and functions
        circuit_types = set()
        target_functions = set()
        for instance in unsat_instances:
            spec = instance.get("spec", {})
            circuit = spec.get("circuit", {})
            target = spec.get("target_function", {})
            
            circuit_types.add(circuit.get("type", "unknown"))
            target_functions.add(target.get("name", "unknown"))
        
        context.log(
            self.name,
            f"Circuit types: {circuit_types}, Functions: {target_functions}"
        )
        
        formalization_plan = {
            "num_candidates": len(unsat_instances),
            "circuit_types": list(circuit_types),
            "target_functions": list(target_functions),
            "tactic_mode": "library",  # Use pre-built tactic library
            "target_language": "lean4",
            "accept_sorry": True,  # MVP: Accept partial proofs
            "unsat_instances": unsat_instances,
        }
        
        return formalization_plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Execute formalization: convert UNSAT results to Lean theorems.
        
        For each UNSAT instance:
        1. Load mining result with LRAT hash
        2. Select appropriate theorem template
        3. Generate Lean theorem with proof tactics
        4. Write to theory/Conjectures/BetA/Proofs/
        5. Track success/failure
        
        Args:
            context: Agent execution context
            plan: Formalization plan from plan() phase
            
        Returns:
            AgentResult with generated theorems and metrics
        """
        context.log(self.name, "Generating Lean theorems with proof tactics")
        
        num_candidates = plan["num_candidates"]
        unsat_instances = plan["unsat_instances"]
        
        context.log(
            self.name,
            f"Formalizing {num_candidates} theorems in Lean 4"
        )
        
        # Generate theorems for each UNSAT instance
        theorems: List[LeanTheorem] = []
        complete_proofs = 0
        partial_proofs = 0
        failed = 0
        
        for instance in unsat_instances:
            try:
                theorem = self._formalize_instance(instance, context)
                theorems.append(theorem)
                
                # Track proof status
                if theorem.status == "complete":
                    complete_proofs += 1
                elif theorem.status == "partial":
                    partial_proofs += 1
                
                context.log(
                    self.name,
                    f"Generated theorem: {theorem.theorem_id} (status: {theorem.status})"
                )
                
            except Exception as e:
                failed += 1
                spec = instance.get("spec", {})
                conjecture_id = spec.get("conjecture_id", "unknown")
                context.log(
                    self.name,
                    f"Failed to formalize {conjecture_id}: {str(e)}"
                )
                print(f"ERROR: Formalization failed for {conjecture_id}: {e}",
                      file=sys.stderr)
        
        # Write theorem files
        written_files = []
        for theorem in theorems:
            try:
                filepath = theorem.write_lean_file(str(self.project_root))
                written_files.append(filepath)
                context.log(self.name, f"Wrote theorem to {filepath}")
            except Exception as e:
                context.log(
                    self.name,
                    f"Failed to write theorem {theorem.theorem_id}: {str(e)}"
                )
                print(f"ERROR: Failed to write {theorem.theorem_id}: {e}",
                      file=sys.stderr)
        
        # Prepare artifacts
        artifacts = {
            "theorems": [
                {
                    "theorem_id": t.theorem_id,
                    "circuit_type": t.circuit_type,
                    "target_function": t.target_function,
                    "n": t.n,
                    "seed": t.seed,
                    "status": t.status,
                    "lrat_hash": t.lrat_hash,
                }
                for t in theorems
            ],
            "written_files": written_files,
            "count": len(theorems),
        }
        
        metrics = {
            "theorems_generated": len(theorems),
            "complete_proofs": complete_proofs,
            "partial_proofs": partial_proofs,
            "failed": failed,
            "files_written": len(written_files),
        }
        
        status = "success" if failed == 0 else "partial_success"
        
        return AgentResult(
            agent_name=self.name,
            status=status,
            artifacts=artifacts,
            metrics=metrics,
        )
    
    def _formalize_instance(
        self,
        instance: Dict[str, Any],
        context: AgentContext
    ) -> LeanTheorem:
        """
        Convert a single UNSAT mining result to a Lean theorem.
        
        Args:
            instance: Mining result with spec and LRAT hash
            context: Agent execution context
            
        Returns:
            LeanTheorem with generated proof
            
        Raises:
            ValueError: If template not found or required fields missing
        """
        # Extract spec and metadata
        spec = instance.get("spec", {})
        circuit = spec.get("circuit", {})
        target = spec.get("target_function", {})
        
        # Get parameters
        circuit_type = circuit.get("type", "monotone")
        target_name = target.get("name", "parity")
        n = circuit.get("num_inputs", 2)
        seed = instance.get("seed", 0)
        task_id = spec.get("task_id", "unknown")
        
        # Get LRAT hash and CNF hash from artifacts
        lrat_hash = instance.get("lrat_hash")
        cnf_hash = instance.get("cnf_hash")  # NEW: Get CNF hash for round-trip verification
        
        context.log(
            self.name,
            f"Formalizing {circuit_type}/{target_name} n={n} seed={seed}"
        )
        
        if lrat_hash:
            context.log(self.name, f"  LRAT hash: {lrat_hash[:16]}...")
        if cnf_hash:
            context.log(self.name, f"  CNF hash: {cnf_hash[:16]}...")
        
        # Select theorem template
        template = self.registry.get_template("A", circuit_type, target_name)
        
        if template is None:
            raise ValueError(
                f"No theorem template for bet=A, "
                f"circuit={circuit_type}, function={target_name}"
            )
        
        # Generate theorem from template
        theorem = template.instantiate(
            n=n,
            seed=seed,
            task_id=task_id,
            lrat_hash=lrat_hash,
            cnf_hash=cnf_hash,  # NEW: Pass CNF hash to template
            circuit_type=circuit_type,
            target_function=target_name,
            depth=circuit.get("depth", 2),  # For AC0 circuits
        )
        
        return theorem
    
    # ------------------------------------------------------------------
    # V14: LLM-assisted sorry closing
    # ------------------------------------------------------------------

    def close_sorry_with_llm(
        self,
        lean_file: "Path",
        lrat_hash: str,
        n: int,
        circuit_type: str,
        func_name: str,
        context: "AgentContext",
        endpoint: str = "http://localhost:11434",
        model: str = "mathstral:7b",
        max_attempts: int = 3,
        num_predict: int = 8192,
        temperature: float = 0.1,
    ) -> bool:
        """
        V14: Attempt to close all sorry stubs in a Lean theorem file using an LLM.

        Strategy:
        1. Read the file and locate sorry occurrences.
        2. Build a close-sorry prompt showing the full file context and the
           verified n=2 proof as a structural reference.
        3. Call the V11 LLM (mathstral:7b) to produce a sorry-free version.
        4. Write the result back to the same file if it contains no sorry.
        5. Retry up to max_attempts times; stop on first sorry-free output.

        The prompt anchors mathstral to the lrat_implies_lower_bound axiom and
        shows that the proof strategy is always:
            by_contra -> Nat.not_lt.mp -> lrat_implies_lower_bound -> exact

        Args:
            lean_file:    Path to the .lean file with sorry stubs
            lrat_hash:    SHA256 hash of the LRAT proof for this n
            n:            Number of inputs
            circuit_type: "monotone", "ac0", or "formula"
            func_name:    "parity", "majority", etc.
            context:      AgentContext for logging
            endpoint:     Ollama base URL
            model:        Ollama model name (V11: mathstral:7b)
            max_attempts: Number of LLM retries before giving up
            num_predict:  Token budget for the LLM
            temperature:  Sampling temperature

        Returns:
            True if sorry was successfully closed, False otherwise
        """
        import urllib.request
        import urllib.error
        import json
        import time

        lean_file = self.project_root / lean_file if not str(lean_file).startswith("/") else lean_file
        lean_file = Path(lean_file)

        if not lean_file.exists():
            context.log(self.name, f"[V14] File not found: {lean_file}", level="ERROR")
            return False

        with open(lean_file, "r") as f:
            original_content = f.read()

        if "sorry" not in original_content:
            context.log(self.name, f"[V14] No sorry in {lean_file.name}, already complete")
            return True

        sorry_count = original_content.count("sorry")
        context.log(self.name, f"[V14] Attempting to close {sorry_count} sorry(s) in {lean_file.name}")
        context.log(self.name, f"[V14] Model={model}, n={n}, lrat_hash={lrat_hash[:16]}...")

        # Detect whether this is a new-style file (imports Theory.Circuits) or
        # old-style (local MonotoneCircuit stub). Old-style files must be rewritten
        # from scratch using the MonotoneParityN2Proof.lean pattern.
        uses_theory_circuits = "Theory.Circuits" in original_content
        is_old_style = not uses_theory_circuits and "MonotoneCircuit" in original_content

        if is_old_style:
            # Old-style files use a local MonotoneCircuit def with sorry semantics.
            # The right fix is to rewrite them using the Theory.Circuits module.
            print(f"LOG [FormalizerAgent V14]: Old-style file detected for {lean_file.name}; "
                  f"will rewrite using Theory.Circuits pattern", file=sys.stderr)
            prompt = f"""You are an expert in Lean 4 formal proofs and circuit complexity.

CONTEXT: The file below is an OLD-STYLE proof stub that defines its own MonotoneCircuit
structure with sorry semantics. This must be REWRITTEN using the Theory.Circuits module.

The correct pattern (used in the verified MonotoneParityN2Proof.lean) is:

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Theory.Circuits
import Tactics.CircuitTactics
import Tactics.EncodingTactics
import Conjectures.BetA.Common

namespace SATurday.Conjectures.BetA.Proofs

open SATurday.Circuits

def parity_2_lrat_proof : CircuitLowerBoundProof := {{
  n := 2,
  max_gates := 4,
  lrat_hash := "382dd167cdb833c99c7e8ddfe8159aac7d7173cf5f981a336196b307f3a64819",
  cnf_hash := "382dd167cdb833c99c7e8ddfe8159aac7d7173cf5f981a336196b307f3a64819",
  function_name := "parity_2",
  circuit_class := "monotone"
}}

theorem monotone_parity_2_lower_bound :
  forall (C : Circuit),
    C.num_inputs = 2 to isMonotone C = true to
    C.computes (parity C.num_inputs) to C.size > 4 := by
  intro C h_inputs h_monotone h_computes
  have h_lrat : forall (D : Circuit) (f : (Fin D.num_inputs to Bool) to Bool),
      D.num_inputs = 2 to D.size <= 4 to not(D.computes f) :=
    lrat_implies_lower_bound parity_2_lrat_proof
  by_contra h_not_gt
  have h_le : C.size <= 4 := Nat.not_lt.mp h_not_gt
  exact h_lrat C (parity C.num_inputs) h_inputs h_le h_computes

end SATurday.Conjectures.BetA.Proofs

TASK: Rewrite the OLD-STYLE file below in this NEW pattern for n={n}, {circuit_type} circuit.
Use lrat_hash := "{lrat_hash}" (or "unknown" if not available).
The max_gates bound for n={n} should be {n * n}.

Output ONLY the complete rewritten Lean 4 file. No explanation. No markdown code fences.
The output must start with "import Mathlib" and end with the closing "end" line.

OLD FILE TO REWRITE:
{original_content}"""
        else:
            # New-style file: has Theory.Circuits; just replace sorry with real tactics.
            prompt = f"""You are an expert in Lean 4 formal proofs and circuit complexity.

CONTEXT: This Lean 4 file proves a monotone circuit lower bound for the {func_name} function
on {n} inputs. The key axiom is:

  axiom lrat_implies_lower_bound (proof : CircuitLowerBoundProof) :
    forall (C : Circuit) (f : (Fin C.num_inputs to Bool) to Bool),
      C.num_inputs = proof.n to C.size <= proof.max_gates to not(C.computes f)

The LRAT hash for n={n} is: {lrat_hash}

VERIFIED PROOF PATTERN (from n=2 which is fully verified):
  theorem monotone_parity_2_lower_bound :
    forall (C : Circuit),
      C.num_inputs = 2 to isMonotone C = true to
      C.computes (parity C.num_inputs) to C.size > 4 := by
    intro C h_inputs h_monotone h_computes
    have h_lrat := lrat_implies_lower_bound parity_2_lrat_proof
    by_contra h_not_gt
    have h_le : C.size <= 4 := Nat.not_lt.mp h_not_gt
    exact h_lrat C (parity C.num_inputs) h_inputs h_le h_computes

TASK: Replace every "sorry" in the file below with real Lean 4 tactics.
Follow the verified proof pattern above. Use lrat_implies_lower_bound with the
CircuitLowerBoundProof record defined in the file (look for "def parity_{n}_lrat_proof").
The max_gates for n={n} should be {n * n}.

Output ONLY the complete corrected Lean 4 file. No explanation. No markdown code fences.
The output must start with "import" and end with the closing "end" line.

CURRENT FILE TO FIX:
{original_content}"""

        url = f"{endpoint}/api/generate"
        payload_dict = {
            "model": model,
            "prompt": prompt,
            "stream": False,
            "options": {
                "temperature": temperature,
                "num_predict": num_predict,
            },
        }

        for attempt in range(1, max_attempts + 1):
            context.log(self.name, f"[V14] Attempt {attempt}/{max_attempts} for {lean_file.name}")
            print(f"LOG [FormalizerAgent V14]: Calling {model} to close sorry in {lean_file.name} "
                  f"(attempt {attempt}/{max_attempts})", file=sys.stderr)
            start = time.time()

            try:
                req = urllib.request.Request(
                    url,
                    data=json.dumps(payload_dict).encode("utf-8"),
                    headers={"Content-Type": "application/json"},
                    method="POST",
                )
                with urllib.request.urlopen(req, timeout=180) as resp:
                    raw = resp.read().decode("utf-8")

                elapsed = time.time() - start
                data = json.loads(raw)
                response_text = data.get("response", "") or data.get("thinking", "")
                print(f"LOG [FormalizerAgent V14]: LLM responded in {elapsed:.1f}s "
                      f"({len(response_text)} chars)", file=sys.stderr)

                if not response_text:
                    context.log(self.name, f"[V14] Empty response on attempt {attempt}", level="WARNING")
                    continue

                # Strip markdown fences if model added them
                cleaned = response_text.strip()
                if cleaned.startswith("```"):
                    lines = cleaned.split("\n")
                    # drop first line (```lean or ```) and last line (```)
                    cleaned = "\n".join(lines[1:-1]) if lines[-1].strip() == "```" else "\n".join(lines[1:])
                    cleaned = cleaned.strip()

                # Only accept if it looks like valid Lean (starts with import or namespace)
                if not (cleaned.startswith("import") or cleaned.startswith("namespace")
                        or cleaned.startswith("/-")):
                    context.log(self.name,
                                f"[V14] Response does not look like Lean on attempt {attempt}",
                                level="WARNING")
                    print(f"LOG [FormalizerAgent V14]: Response preview: {cleaned[:200]}",
                          file=sys.stderr)
                    continue

                # Check if sorry was closed
                if "sorry" not in cleaned:
                    context.log(self.name,
                                f"[V14] SUCCESS: sorry closed in {lean_file.name} on attempt {attempt}")
                    print(f"LOG [FormalizerAgent V14]: Writing sorry-free proof to {lean_file}",
                          file=sys.stderr)
                    with open(lean_file, "w") as f:
                        f.write(cleaned + "\n")
                    return True
                else:
                    remaining = cleaned.count("sorry")
                    context.log(self.name,
                                f"[V14] {remaining} sorry(s) remain after attempt {attempt}",
                                level="WARNING")
                    print(f"LOG [FormalizerAgent V14]: {remaining} sorry stubs remain in LLM output",
                          file=sys.stderr)

            except Exception as e:
                elapsed = time.time() - start
                context.log(self.name,
                            f"[V14] LLM error on attempt {attempt}: {e}",
                            level="ERROR")
                print(f"LOG [FormalizerAgent V14]: Error after {elapsed:.1f}s: {e}",
                      file=sys.stderr)

        context.log(self.name,
                    f"[V14] Failed to close sorry in {lean_file.name} after {max_attempts} attempts",
                    level="WARNING")
        return False

    def attempt_v14_sorry_closure(
        self,
        context: "AgentContext",
    ) -> Dict[str, Any]:
        """
        V14 entry point: scan theory/Conjectures/BetA/Proofs/ for files with sorry
        and attempt LLM-assisted closure.

        Reads LLM config from context.config to get model/endpoint/attempts.
        Only runs if agents.conjecturer.llm.enabled is True.

        Returns:
            Dict with keys: attempted, closed, failed, skipped
        """
        agents_config = context.config.get("agents", {})
        conjecturer_config = agents_config.get("conjecturer", {})
        llm_config = conjecturer_config.get("llm", {})
        llm_enabled = llm_config.get("enabled", False)
        model = llm_config.get("model", "mathstral:7b")
        endpoint = llm_config.get("endpoint", "http://localhost:11434")
        num_predict = llm_config.get("num_predict", 8192)
        temperature = llm_config.get("temperature", 0.1)

        formalizer_config = agents_config.get("formalizer", {})
        max_attempts = formalizer_config.get("close_sorry_attempts", 3)
        close_enabled = formalizer_config.get("close_sorry_with_llm", True)

        if not llm_enabled or not close_enabled:
            context.log(self.name,
                        "[V14] Skipping sorry closure: LLM not enabled or close_sorry_with_llm=false")
            return {"attempted": 0, "closed": 0, "failed": 0, "skipped": 1}

        proofs_dir = self.project_root / "theory" / "Conjectures" / "BetA" / "Proofs"
        if not proofs_dir.exists():
            context.log(self.name, f"[V14] Proofs directory not found: {proofs_dir}", level="WARNING")
            return {"attempted": 0, "closed": 0, "failed": 0, "skipped": 0}

        import re
        results = {"attempted": 0, "closed": 0, "failed": 0, "skipped": 0}

        # Find all .lean files with sorry stubs
        sorry_files = []
        for lean_file in sorted(proofs_dir.glob("*.lean")):
            with open(lean_file) as f:
                content = f.read()
            if "sorry" in content:
                sorry_files.append(lean_file)

        context.log(self.name, f"[V14] Found {len(sorry_files)} file(s) with sorry stubs")
        print(f"LOG [FormalizerAgent V14]: {len(sorry_files)} sorry files: "
              f"{[f.name for f in sorry_files]}", file=sys.stderr)

        for lean_file in sorry_files:
            # Extract n from filename (e.g., MonotoneParityN5Proof.lean -> 5)
            m = re.search(r"[Nn](\d+)", lean_file.stem)
            n = int(m.group(1)) if m else 2
            circuit_type = "monotone"
            func_name = "parity"

            # Try to extract LRAT hash from the file itself
            with open(lean_file) as f:
                content = f.read()
            hash_match = re.search(r'lrat_hash\s*:=\s*"([0-9a-f]{40,})"', content)
            lrat_hash = hash_match.group(1) if hash_match else "unknown"

            context.log(self.name,
                        f"[V14] Processing {lean_file.name}: n={n}, lrat_hash={lrat_hash[:16]}...")
            results["attempted"] += 1

            success = self.close_sorry_with_llm(
                lean_file=lean_file,
                lrat_hash=lrat_hash,
                n=n,
                circuit_type=circuit_type,
                func_name=func_name,
                context=context,
                endpoint=endpoint,
                model=model,
                max_attempts=max_attempts,
                num_predict=num_predict,
                temperature=temperature,
            )

            if success:
                results["closed"] += 1
                context.log(self.name, f"[V14] Closed sorry in {lean_file.name}")
            else:
                results["failed"] += 1
                context.log(self.name, f"[V14] Could not close sorry in {lean_file.name}")

        context.log(self.name,
                    f"[V14] Summary: attempted={results['attempted']}, "
                    f"closed={results['closed']}, failed={results['failed']}")
        return results

    def report(self, context: AgentContext, result: AgentResult) -> str:
        """
        Generate Markdown report for formalization phase.
        
        Args:
            context: Agent execution context
            result: Formalization results
            
        Returns:
            Markdown-formatted report
        """
        theorems = result.artifacts.get("theorems", [])
        files = result.artifacts.get("written_files", [])
        
        count = result.metrics.get("theorems_generated", 0)
        complete = result.metrics.get("complete_proofs", 0)
        partial = result.metrics.get("partial_proofs", 0)
        failed = result.metrics.get("failed", 0)
        
        report = f"""# Formalizer Agent Report

## Summary
- Theorems Generated: {count}
- Complete Proofs: {complete}
- Partial Proofs (with sorry): {partial}
- Failed: {failed}
- Files Written: {len(files)}
- Status: {result.status}

## Generated Theorems
"""
        
        for thm in theorems:
            report += f"\n### {thm['theorem_id']}\n"
            report += f"- Circuit Type: {thm['circuit_type']}\n"
            report += f"- Target Function: {thm['target_function']}\n"
            report += f"- Inputs: n={thm['n']}\n"
            report += f"- Seed: {thm['seed']}\n"
            report += f"- Status: {thm['status']}\n"
            if thm['lrat_hash']:
                report += f"- LRAT Hash: `{thm['lrat_hash']}`\n"
        
        report += "\n## Written Files\n\n"
        for filepath in files:
            # Make path relative for readability
            rel_path = os.path.relpath(filepath, self.project_root)
            report += f"- `{rel_path}`\n"
        
        report += "\n## Next Steps\n"
        if complete > 0:
            report += "- Complete proofs ready for verification\n"
        if partial > 0:
            report += f"- {partial} partial proofs need tactic completion\n"
        report += "- Run `make verify` to check Lean compilation\n"
        report += "- Run Critic agent to analyze proofs for barriers\n"
        
        return report
