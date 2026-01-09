"""
Conjecturer Agent - Template-based conjecture generation.

This agent generates conjectures using:
- Grammar-driven templates (MVP)
- Optional local LLM (future)

Outputs:
- Lean theorem stubs
- CNF specifications for mining
"""

from typing import Any, Dict
from .core import AgentBase, AgentContext, AgentResult


class ConjecturerAgent(AgentBase):
    """
    Template-based conjecture generator.
    
    For MVP: Uses simple templates; no LLM required.
    """
    
    def __init__(self):
        super().__init__("conjecturer")
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Plan conjecture generation based on tasks from planner.
        """
        context.log(self.name, "Planning conjecture generation")
        
        # Get plan from planner artifacts
        planner_artifacts = context.artifacts.get("planner", {})
        plan = planner_artifacts.get("plan", {})
        tasks = plan.get("tasks", [])
        
        context.log(self.name, f"Received {len(tasks)} tasks from planner")
        
        # For MVP stub: Just acknowledge tasks
        generation_plan = {
            "num_tasks": len(tasks),
            "mode": "template",  # vs "llm"
            "template_type": "circuit_lower_bound",
        }
        
        return generation_plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Generate conjectures using templates.
        
        For MVP stub: Log generation without creating actual files.
        """
        context.log(self.name, "Generating conjectures from templates")
        
        num_tasks = plan["num_tasks"]
        context.log(self.name, f"Template mode: generating {num_tasks} conjectures")
        
        # Stub: Simulate conjecture generation
        conjectures = []
        for i in range(min(num_tasks, 3)):  # Limit to 3 for stub
            conjecture = {
                "id": f"conj_{i}",
                "lean_stub": f"theorem stub_{i} : ∀ n, circuit_size n ≥ lower_bound n := sorry",
                "cnf_spec": f"circuit_encoding_{i}.cnf",
            }
            conjectures.append(conjecture)
            context.log(self.name, f"Generated conjecture: {conjecture['id']}")
        
        artifacts = {
            "conjectures": conjectures,
            "count": len(conjectures),
        }
        
        metrics = {
            "num_generated": len(conjectures),
            "template_type": plan["template_type"],
        }
        
        return AgentResult(
            agent_name=self.name,
            status="success",
            artifacts=artifacts,
            metrics=metrics,
        )
    
    def report(self, context: AgentContext, result: AgentResult) -> str:
        """Generate Markdown report for conjecture generation."""
        conjectures = result.artifacts.get("conjectures", [])
        count = result.metrics.get("num_generated", 0)
        
        report = f"""# Conjecturer Agent Report

## Summary
- Conjectures Generated: {count}
- Mode: Template-based
- Status: {result.status}

## Generated Conjectures
"""
        
        for conj in conjectures:
            report += f"\n### {conj['id']}\n"
            report += f"- Lean stub: `{conj['lean_stub']}`\n"
            report += f"- CNF spec: `{conj['cnf_spec']}`\n"
        
        report += "\n## Next Steps\nConjectures ready for Miner agent to test.\n"
        
        return report

