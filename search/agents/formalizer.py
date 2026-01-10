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
        
        # Get LRAT hash from artifacts
        lrat_hash = instance.get("lrat_hash")
        
        context.log(
            self.name,
            f"Formalizing {circuit_type}/{target_name} n={n} seed={seed}"
        )
        
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
            circuit_type=circuit_type,
            target_function=target_name,
            depth=circuit.get("depth", 2),  # For AC0 circuits
        )
        
        return theorem
    
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
