"""
Planner Agent - Rule-based task decomposition.

This agent decomposes research bets into concrete tasks with:
- Circuit types and size ranges
- Random seeds for determinism
- Acceptance criteria

For MVP: Uses hard-coded rules; no LLM required.
"""

from typing import Any, Dict
from .core import AgentBase, AgentContext, AgentResult


class PlannerAgent(AgentBase):
    """
    Rule-based planner that decomposes research bets into testable tasks.
    """
    
    def __init__(self):
        super().__init__("planner")
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Create a planning strategy based on the research bet.
        
        For MVP: Generate a simple task matrix for small problem sizes.
        """
        context.log(self.name, "Planning task decomposition")
        
        # Extract configuration
        bet = context.config.get("bet", "A")
        max_size = context.config.get("max_size", 10)
        num_seeds = context.config.get("num_seeds", 3)
        
        context.log(self.name, f"Target bet: {bet}")
        context.log(self.name, f"Max problem size: {max_size}")
        context.log(self.name, f"Number of seeds: {num_seeds}")
        
        # Create task matrix
        tasks = []
        for n in range(2, max_size + 1):
            for seed_offset in range(num_seeds):
                task_seed = context.seed + seed_offset
                tasks.append({
                    "problem_size": n,
                    "seed": task_seed,
                    "bet": bet,
                })
        
        plan = {
            "bet": bet,
            "total_tasks": len(tasks),
            "tasks": tasks,
            "strategy": "exhaustive_small_n",
        }
        
        context.log(self.name, f"Generated {len(tasks)} tasks")
        
        return plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Execute planning: validate plan and prepare for next agents.
        
        For MVP stub: Just log and return success.
        """
        context.log(self.name, "Executing plan validation")
        
        total_tasks = plan["total_tasks"]
        context.log(self.name, f"Plan validated: {total_tasks} tasks ready")
        
        # Store plan in artifacts for downstream agents
        artifacts = {
            "plan": plan,
            "status": "ready",
        }
        
        metrics = {
            "total_tasks": total_tasks,
            "bet": plan["bet"],
        }
        
        return AgentResult(
            agent_name=self.name,
            status="success",
            artifacts=artifacts,
            metrics=metrics,
        )
    
    def report(self, context: AgentContext, result: AgentResult) -> str:
        """Generate Markdown report for planning phase."""
        plan = result.artifacts.get("plan", {})
        total_tasks = result.metrics.get("total_tasks", 0)
        bet = result.metrics.get("bet", "unknown")
        
        report = f"""# Planner Agent Report

## Summary
- Research Bet: {bet}
- Total Tasks: {total_tasks}
- Status: {result.status}

## Task Breakdown
Strategy: {plan.get('strategy', 'unknown')}

Generated {total_tasks} tasks for exploration.

## Next Steps
Tasks are ready for Conjecturer agent to generate candidates.
"""
        
        return report

