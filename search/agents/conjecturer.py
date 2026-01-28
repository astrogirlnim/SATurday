"""
Conjecturer Agent - Template-based conjecture generation.

This agent generates conjectures using:
- Grammar-driven templates (MVP)
- Optional local LLM (future)

Outputs:
- Lean theorem stubs written to theory/Conjectures/
- CNF specifications written to search/specs/

For MVP: Uses bet-specific templates for circuit lower bounds.
"""

from typing import Any, Dict, List
from pathlib import Path
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


class ConjecturerAgent(AgentBase):
    """
    Template-based conjecture generator.
    
    Generates conjectures from planner tasks using bet-specific templates.
    For each task:
    1. Selects appropriate template based on bet and circuit type
    2. Instantiates template with task parameters
    3. Generates Lean theorem stub with sorry placeholder
    4. Generates CNF specification for SAT mining
    5. Writes both to output directories
    """
    
    def __init__(self):
        super().__init__("conjecturer")
        self.registry = TemplateRegistry()
        self._register_templates()
        print(f"[ConjecturerAgent] Initialized with {len(self.registry.get_all_templates())} template types")
    
    def _register_templates(self):
        """Register all available templates."""
        print("[ConjecturerAgent] Registering templates...")
        
        # Bet A: Circuit lower bounds
        # Register templates by (bet, circuit_type, function_name)
        
        # Monotone circuits
        self.registry.register("A", "monotone", "parity", MonotoneParityTemplate())
        self.registry.register("A", "monotone", "majority", MonotoneMajorityTemplate())
        self.registry.register("A", "monotone", "threshold_2", MonotoneThresholdTemplate(threshold_k=2))
        self.registry.register("A", "monotone", "threshold_3", MonotoneThresholdTemplate(threshold_k=3))
        
        # AC0 circuits
        self.registry.register("A", "ac0", "parity", AC0ParityTemplate())
        self.registry.register("A", "ac0", "majority", AC0MajorityTemplate())
        
        # Formula circuits
        self.registry.register("A", "formula", "parity", FormulaParityTemplate())
        
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
        
        for i, task in enumerate(tasks):
            task_id = task.get("task_id", f"task_{i}")
            bet = task.get("bet", "A")
            circuit_type = task.get("circuit_type", "unknown")
            function_name = task.get("function_name", "parity")
            
            context.log(self.name, f"Processing task {i+1}/{len(tasks)}: {task_id}")
            
            try:
                # Get template for this bet, circuit type, and function
                template = registry.get_template(bet, circuit_type, function_name)
                
                if not template:
                    context.log(
                        self.name,
                        f"No template for (bet={bet}, circuit_type={circuit_type}, function={function_name})",
                        level="WARNING"
                    )
                    failed_tasks.append(task_id)
                    continue
                
                context.log(self.name, f"Using template: {template.template_id}")
                
                # Instantiate template
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
            "mode": "template",
        }
        
        status = "success" if conjectures else "failure"
        
        return AgentResult(
            agent_name=self.name,
            status=status,
            artifacts=artifacts,
            metrics=metrics,
        )
    
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

