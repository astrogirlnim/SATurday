"""
Planner Agent - Rule-based task decomposition for SATurday research bets.

This agent decomposes research bets into concrete tasks with:
- Bet-specific decomposition strategies
- Circuit types and size ranges (Bet A)
- Algorithm schemas (Bet B)
- Hardness-randomness parameters (Bet C)
- Barrier-aware reduction configurations (Bet D)
- Random seeds for determinism
- Task dependencies and milestones
- Acceptance criteria per task

For MVP: Focuses on Bet A (Circuit Lower Bounds) with full implementation.
Other bets (B, C, D) have stub decomposition for future implementation.
"""

from typing import Any, Dict, List, Optional, Tuple
from dataclasses import dataclass, field
import yaml
from pathlib import Path
from .core import AgentBase, AgentContext, AgentResult


@dataclass
class Task:
    """
    Represents a single task in the research plan.
    
    Attributes:
        task_id: Unique identifier for this task
        bet: Research bet (A, B, C, or D)
        problem_size: Size parameter (e.g., n for circuits)
        seed: Random seed for determinism
        circuit_type: Type of circuit (for Bet A: monotone, ac0, formula)
        algorithm_schema: Algorithm type (for Bet B: sorting, searching, etc.)
        dependencies: List of task_ids that must complete first
        timeout_seconds: Maximum time allowed for this task
        acceptance_criteria: Dict of criteria for task success
        priority: Task priority (1=highest, higher numbers=lower priority)
        estimated_time_seconds: Estimated execution time
    """
    task_id: str
    bet: str
    problem_size: int
    seed: int
    circuit_type: Optional[str] = None
    algorithm_schema: Optional[str] = None
    dependencies: List[str] = field(default_factory=list)
    timeout_seconds: int = 300
    acceptance_criteria: Dict[str, Any] = field(default_factory=dict)
    priority: int = 1
    estimated_time_seconds: int = 10
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert task to dictionary for serialization."""
        return {
            "task_id": self.task_id,
            "bet": self.bet,
            "problem_size": self.problem_size,
            "seed": self.seed,
            "circuit_type": self.circuit_type,
            "algorithm_schema": self.algorithm_schema,
            "dependencies": self.dependencies,
            "timeout_seconds": self.timeout_seconds,
            "acceptance_criteria": self.acceptance_criteria,
            "priority": self.priority,
            "estimated_time_seconds": self.estimated_time_seconds,
        }


@dataclass
class Milestone:
    """
    Represents a milestone in the research plan.
    
    Attributes:
        name: Milestone name
        description: What this milestone represents
        required_tasks: Task IDs that must complete for this milestone
        acceptance: Criteria for milestone completion
    """
    name: str
    description: str
    required_tasks: List[str]
    acceptance: str


class BetDecomposer:
    """
    Bet-specific decomposition logic for different research paths.
    
    Each bet has a unique decomposition strategy:
    - Bet A: Circuit lower bounds (monotone, AC0, formula)
    - Bet B: Algorithm synthesis with proofs
    - Bet C: Hardness-vs-randomness implications
    - Bet D: Barrier-aware reductions
    """
    
    def decompose_bet_a_circuit_bounds(
        self,
        config: Dict[str, Any],
        base_seed: int
    ) -> Tuple[List[Task], List[Milestone]]:
        """
        Decompose Bet A: Circuit Lower Bounds.
        
        Strategy:
        - Generate tasks for multiple circuit types (monotone, AC0, formula)
        - Size progression: 2, 4, 8, ... up to max_size
        - Multiple seeds per size for robustness
        - Parallel tasks for different circuit types
        
        Args:
            config: Configuration dictionary with max_size, num_seeds, etc.
            base_seed: Base random seed for determinism
        
        Returns:
            Tuple of (tasks, milestones)
        """
        print(f"[BetDecomposer] Decomposing Bet A: Circuit Lower Bounds")
        
        # Extract configuration with defaults
        max_size = config.get("max_size", 10)
        num_seeds = config.get("num_seeds", 3)
        
        # Circuit types to explore (MVP: all three)
        circuit_types = config.get("circuit_types", ["monotone", "ac0", "formula"])
        
        # Size progression (powers of 2 for efficiency, plus intermediate values)
        size_progression = self._generate_size_progression(2, max_size)
        
        print(f"[BetDecomposer] Circuit types: {circuit_types}")
        print(f"[BetDecomposer] Size progression: {size_progression}")
        print(f"[BetDecomposer] Seeds per size: {num_seeds}")
        
        tasks = []
        task_counter = 0
        
        # Generate tasks for each circuit type, size, and seed
        for circuit_type in circuit_types:
            for size in size_progression:
                for seed_offset in range(num_seeds):
                    task_seed = base_seed + task_counter
                    task_id = f"bet_a_{circuit_type}_n{size}_s{task_seed}"
                    
                    # Estimate time: larger circuits take longer
                    estimated_time = self._estimate_task_time(size, circuit_type)
                    
                    task = Task(
                        task_id=task_id,
                        bet="A",
                        problem_size=size,
                        seed=task_seed,
                        circuit_type=circuit_type,
                        timeout_seconds=max(estimated_time * 3, 60),  # 3x estimate or 60s min
                        estimated_time_seconds=estimated_time,
                        priority=self._compute_priority(size, circuit_type),
                        acceptance_criteria={
                            "generate_cnf": True,
                            "run_solver": True,
                            "extract_patterns": True,
                        },
                    )
                    
                    tasks.append(task)
                    task_counter += 1
        
        print(f"[BetDecomposer] Generated {len(tasks)} tasks for Bet A")
        
        # Define milestones
        milestones = [
            Milestone(
                name="first_monotone_bound",
                description="First proved lower bound for monotone circuits",
                required_tasks=[t.task_id for t in tasks if t.circuit_type == "monotone"][:3],
                acceptance="At least one UNSAT proof with formalized lower bound",
            ),
            Milestone(
                name="ac0_exploration",
                description="AC0 circuit exploration complete",
                required_tasks=[t.task_id for t in tasks if t.circuit_type == "ac0"],
                acceptance="All AC0 tasks completed with pattern extraction",
            ),
            Milestone(
                name="formula_baseline",
                description="Formula circuit baseline established",
                required_tasks=[t.task_id for t in tasks if t.circuit_type == "formula"][:5],
                acceptance="Formula tasks provide comparison baseline",
            ),
        ]
        
        return tasks, milestones
    
    def decompose_bet_b_algorithms(
        self,
        config: Dict[str, Any],
        base_seed: int
    ) -> Tuple[List[Task], List[Milestone]]:
        """
        Decompose Bet B: Algorithm Synthesis with Proofs.
        
        Strategy:
        - Algorithm schemas: sorting, searching, graph algorithms
        - Generate instances with polynomial-time bounds
        - Prove bounds via recurrence relations and induction
        
        MVP: Stub implementation - returns placeholder tasks.
        
        Args:
            config: Configuration dictionary
            base_seed: Base random seed
        
        Returns:
            Tuple of (tasks, milestones)
        """
        print(f"[BetDecomposer] Decomposing Bet B: Algorithm Synthesis (STUB)")
        
        # Stub: Generate one placeholder task
        task = Task(
            task_id="bet_b_stub_placeholder",
            bet="B",
            problem_size=10,
            seed=base_seed,
            algorithm_schema="sorting",
            acceptance_criteria={"stub": True},
        )
        
        milestone = Milestone(
            name="bet_b_placeholder",
            description="Placeholder milestone for Bet B (not yet implemented)",
            required_tasks=["bet_b_stub_placeholder"],
            acceptance="Stub only - implement in future",
        )
        
        return [task], [milestone]
    
    def decompose_bet_c_hardness_randomness(
        self,
        config: Dict[str, Any],
        base_seed: int
    ) -> Tuple[List[Task], List[Milestone]]:
        """
        Decompose Bet C: Hardness-vs-Randomness Implications.
        
        Strategy:
        - Correlation tests between circuit hardness and PRGs
        - Formalize micro-implications in Lean
        - Explore small circuit sizes with explicit functions
        
        MVP: Stub implementation - returns placeholder tasks.
        
        Args:
            config: Configuration dictionary
            base_seed: Base random seed
        
        Returns:
            Tuple of (tasks, milestones)
        """
        print(f"[BetDecomposer] Decomposing Bet C: Hardness-Randomness (STUB)")
        
        task = Task(
            task_id="bet_c_stub_placeholder",
            bet="C",
            problem_size=10,
            seed=base_seed,
            acceptance_criteria={"stub": True},
        )
        
        milestone = Milestone(
            name="bet_c_placeholder",
            description="Placeholder milestone for Bet C (not yet implemented)",
            required_tasks=["bet_c_stub_placeholder"],
            acceptance="Stub only - implement in future",
        )
        
        return [task], [milestone]
    
    def decompose_bet_d_barriers(
        self,
        config: Dict[str, Any],
        base_seed: int
    ) -> Tuple[List[Task], List[Milestone]]:
        """
        Decompose Bet D: Barrier-Aware Reductions.
        
        Strategy:
        - Design non-relativizing encodings
        - Oracle world diagnostics
        - Test for natural proofs violations
        
        MVP: Stub implementation - returns placeholder tasks.
        
        Args:
            config: Configuration dictionary
            base_seed: Base random seed
        
        Returns:
            Tuple of (tasks, milestones)
        """
        print(f"[BetDecomposer] Decomposing Bet D: Barrier-Aware Reductions (STUB)")
        
        task = Task(
            task_id="bet_d_stub_placeholder",
            bet="D",
            problem_size=10,
            seed=base_seed,
            acceptance_criteria={"stub": True},
        )
        
        milestone = Milestone(
            name="bet_d_placeholder",
            description="Placeholder milestone for Bet D (not yet implemented)",
            required_tasks=["bet_d_stub_placeholder"],
            acceptance="Stub only - implement in future",
        )
        
        return [task], [milestone]
    
    def _generate_size_progression(self, min_size: int, max_size: int) -> List[int]:
        """
        Generate size progression for tasks.
        
        Strategy: Start small (2), then increase gradually.
        For small max_size, use every value.
        For large max_size, use exponential progression.
        
        Args:
            min_size: Minimum problem size
            max_size: Maximum problem size
        
        Returns:
            List of problem sizes
        """
        if max_size <= 10:
            # For small ranges, use all values
            return list(range(min_size, max_size + 1))
        else:
            # For larger ranges, use exponential + selected values
            sizes = []
            current = min_size
            while current <= max_size:
                sizes.append(current)
                if current < 8:
                    current += 1  # Fine-grained for small n
                elif current < 32:
                    current += 2  # Medium steps
                else:
                    current *= 2  # Exponential for large n
            
            # Ensure max_size is included
            if sizes[-1] < max_size:
                sizes.append(max_size)
            
            return sizes
    
    def _estimate_task_time(self, size: int, circuit_type: str) -> int:
        """
        Estimate execution time for a task based on size and type.
        
        Rough heuristics:
        - Small circuits (n <= 5): seconds
        - Medium circuits (n <= 10): tens of seconds
        - Large circuits (n > 10): minutes
        
        Args:
            size: Problem size
            circuit_type: Circuit type
        
        Returns:
            Estimated time in seconds
        """
        base_time = 5  # Base 5 seconds
        
        # Exponential growth with size
        if size <= 5:
            time_factor = size
        elif size <= 10:
            time_factor = size * 2
        else:
            time_factor = size * 5
        
        # Circuit type multiplier
        type_multiplier = {
            "monotone": 1.0,
            "ac0": 1.5,  # AC0 is slightly harder
            "formula": 0.8,  # Formulas are simpler (fan-out 1)
        }.get(circuit_type, 1.0)
        
        return int(base_time * time_factor * type_multiplier)
    
    def _compute_priority(self, size: int, circuit_type: str) -> int:
        """
        Compute task priority (1=highest).
        
        Strategy: Prioritize smaller sizes and simpler circuit types first.
        
        Args:
            size: Problem size
            circuit_type: Circuit type
        
        Returns:
            Priority (1=highest, higher numbers=lower priority)
        """
        # Smaller sizes have higher priority
        size_priority = (size + 1) // 2
        
        # Circuit type priority
        type_priority = {
            "monotone": 0,  # Start with monotone
            "formula": 1,   # Then formula
            "ac0": 2,       # AC0 last (most complex)
        }.get(circuit_type, 1)
        
        return size_priority + type_priority


class PlanValidator:
    """
    Validates research plans for correctness and feasibility.
    
    Checks:
    - No circular dependencies
    - All tasks have valid parameters
    - Resource limits are reasonable
    - Acceptance criteria are defined
    """
    
    def validate(self, tasks: List[Task], milestones: List[Milestone]) -> Tuple[bool, List[str]]:
        """
        Validate a research plan.
        
        Args:
            tasks: List of tasks to validate
            milestones: List of milestones to validate
        
        Returns:
            Tuple of (is_valid, error_messages)
        """
        print(f"[PlanValidator] Validating plan with {len(tasks)} tasks and {len(milestones)} milestones")
        
        errors = []
        
        # Check 1: No empty task list
        if not tasks:
            errors.append("Plan has no tasks")
            return False, errors
        
        # Check 2: All tasks have unique IDs
        task_ids = [t.task_id for t in tasks]
        if len(task_ids) != len(set(task_ids)):
            errors.append("Duplicate task IDs found")
        
        # Check 3: All tasks have valid parameters
        for task in tasks:
            if task.problem_size < 1:
                errors.append(f"Task {task.task_id} has invalid problem_size: {task.problem_size}")
            if task.timeout_seconds < 1:
                errors.append(f"Task {task.task_id} has invalid timeout: {task.timeout_seconds}")
            if not task.bet in ["A", "B", "C", "D"]:
                errors.append(f"Task {task.task_id} has invalid bet: {task.bet}")
        
        # Check 4: Dependencies reference valid tasks
        task_id_set = set(task_ids)
        for task in tasks:
            for dep in task.dependencies:
                if dep not in task_id_set:
                    errors.append(f"Task {task.task_id} references invalid dependency: {dep}")
        
        # Check 5: No circular dependencies (simple check - no self-loops)
        for task in tasks:
            if task.task_id in task.dependencies:
                errors.append(f"Task {task.task_id} has circular dependency (self-loop)")
        
        # Check 6: Milestones reference valid tasks
        for milestone in milestones:
            for task_id in milestone.required_tasks:
                if task_id not in task_id_set:
                    errors.append(f"Milestone {milestone.name} references invalid task: {task_id}")
        
        if errors:
            print(f"[PlanValidator] Validation FAILED with {len(errors)} errors")
            return False, errors
        
        print(f"[PlanValidator] Validation PASSED")
        return True, []


class PlannerAgent(AgentBase):
    """
    Rule-based planner that decomposes research bets into testable tasks.
    
    The planner:
    1. Analyzes the research bet (A, B, C, or D)
    2. Generates bet-specific tasks using decomposition rules
    3. Validates the plan for correctness
    4. Generates YAML plan file for persistence
    5. Provides milestone tracking for progress monitoring
    """
    
    def __init__(self):
        super().__init__("planner")
        self.decomposer = BetDecomposer()
        self.validator = PlanValidator()
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Create a planning strategy based on the research bet.
        
        Phase 1: Planning
        - Extract bet and configuration
        - Decompose bet into tasks using bet-specific rules
        - Generate milestones
        - Validate plan
        
        Args:
            context: Agent execution context with config
        
        Returns:
            Dictionary with plan details (tasks, milestones, strategy)
        """
        context.log(self.name, "=== PHASE 1: PLANNING ===")
        context.log(self.name, "Starting task decomposition")
        
        # Extract configuration
        bet = context.config.get("bet", "A")
        max_size = context.config.get("max_size", 10)
        num_seeds = context.config.get("num_seeds", 3)
        
        context.log(self.name, f"Target bet: {bet}")
        context.log(self.name, f"Max problem size: {max_size}")
        context.log(self.name, f"Number of seeds per size: {num_seeds}")
        
        # Decompose bet into tasks and milestones
        context.log(self.name, f"Decomposing Bet {bet}...")
        
        if bet == "A":
            tasks, milestones = self.decomposer.decompose_bet_a_circuit_bounds(
                context.config, context.seed
            )
            strategy = "circuit_lower_bounds"
        elif bet == "B":
            tasks, milestones = self.decomposer.decompose_bet_b_algorithms(
                context.config, context.seed
            )
            strategy = "algorithm_synthesis"
        elif bet == "C":
            tasks, milestones = self.decomposer.decompose_bet_c_hardness_randomness(
                context.config, context.seed
            )
            strategy = "hardness_randomness"
        elif bet == "D":
            tasks, milestones = self.decomposer.decompose_bet_d_barriers(
                context.config, context.seed
            )
            strategy = "barrier_aware_reductions"
        else:
            context.log(self.name, f"ERROR: Unknown bet '{bet}', defaulting to Bet A", level="ERROR")
            tasks, milestones = self.decomposer.decompose_bet_a_circuit_bounds(
                context.config, context.seed
            )
            strategy = "circuit_lower_bounds_fallback"
        
        context.log(self.name, f"Generated {len(tasks)} tasks and {len(milestones)} milestones")
        
        # Validate plan
        context.log(self.name, "Validating plan...")
        is_valid, errors = self.validator.validate(tasks, milestones)
        
        if not is_valid:
            context.log(self.name, f"Plan validation FAILED: {errors}", level="ERROR")
            # For MVP, continue anyway but log the errors
            for error in errors:
                context.log(self.name, f"  - {error}", level="ERROR")
        else:
            context.log(self.name, "Plan validation PASSED")
        
        # Compute statistics
        total_estimated_time = sum(t.estimated_time_seconds for t in tasks)
        
        context.log(self.name, f"Total estimated time: {total_estimated_time} seconds ({total_estimated_time/60:.1f} minutes)")
        
        # Build plan dictionary
        plan = {
            "bet": bet,
            "strategy": strategy,
            "total_tasks": len(tasks),
            "total_milestones": len(milestones),
            "total_estimated_time_seconds": total_estimated_time,
            "tasks": [t.to_dict() for t in tasks],
            "milestones": [
                {
                    "name": m.name,
                    "description": m.description,
                    "required_tasks": m.required_tasks,
                    "acceptance": m.acceptance,
                }
                for m in milestones
            ],
            "validation": {
                "is_valid": is_valid,
                "errors": errors,
            },
        }
        
        context.log(self.name, "Planning phase complete")
        
        return plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Execute planning: validate plan, generate YAML, and prepare artifacts.
        
        Phase 2: Acting
        - Final validation check
        - Generate YAML plan file (optional, for persistence)
        - Store plan in artifacts for downstream agents
        
        Args:
            context: Agent execution context
            plan: Plan from plan() phase
        
        Returns:
            AgentResult with status and artifacts
        """
        context.log(self.name, "=== PHASE 2: ACTING ===")
        context.log(self.name, "Executing plan finalization")
        
        total_tasks = plan["total_tasks"]
        bet = plan["bet"]
        strategy = plan["strategy"]
        
        context.log(self.name, f"Finalizing plan: {total_tasks} tasks for Bet {bet}")
        
        # Generate YAML plan file (optional, for reference)
        yaml_generated = self._generate_yaml_plan(context, plan)
        
        if yaml_generated:
            context.log(self.name, "YAML plan file generated successfully")
        else:
            context.log(self.name, "YAML plan generation skipped (optional)", level="INFO")
        
        # Store plan in artifacts for downstream agents
        artifacts = {
            "plan": plan,
            "status": "ready",
            "yaml_generated": yaml_generated,
        }
        
        # Compute metrics
        metrics = {
            "total_tasks": total_tasks,
            "total_milestones": plan["total_milestones"],
            "bet": bet,
            "strategy": strategy,
            "estimated_time_seconds": plan["total_estimated_time_seconds"],
            "estimated_time_minutes": plan["total_estimated_time_seconds"] / 60,
            "validation_passed": plan["validation"]["is_valid"],
        }
        
        context.log(self.name, "Plan ready for downstream agents")
        context.log(self.name, f"Next: Conjecturer will process {total_tasks} tasks")
        
        return AgentResult(
            agent_name=self.name,
            status="success",
            artifacts=artifacts,
            metrics=metrics,
        )
    
    def report(self, context: AgentContext, result: AgentResult) -> str:
        """
        Generate Markdown report for planning phase.
        
        Phase 3: Reporting
        - Summary statistics
        - Task breakdown by type
        - Milestone descriptions
        - Validation status
        
        Args:
            context: Agent execution context
            result: Result from act() phase
        
        Returns:
            Markdown-formatted report string
        """
        context.log(self.name, "=== PHASE 3: REPORTING ===")
        context.log(self.name, "Generating plan report")
        
        plan = result.artifacts.get("plan", {})
        total_tasks = result.metrics.get("total_tasks", 0)
        total_milestones = result.metrics.get("total_milestones", 0)
        bet = result.metrics.get("bet", "unknown")
        strategy = result.metrics.get("strategy", "unknown")
        estimated_time_minutes = result.metrics.get("estimated_time_minutes", 0)
        validation_passed = result.metrics.get("validation_passed", False)
        
        # Count tasks by type
        tasks = plan.get("tasks", [])
        task_by_type = {}
        for task in tasks:
            task_type = task.get("circuit_type") or task.get("algorithm_schema") or "other"
            task_by_type[task_type] = task_by_type.get(task_type, 0) + 1
        
        # Build task breakdown table
        task_breakdown_rows = "\n".join([
            f"| {task_type} | {count} |"
            for task_type, count in sorted(task_by_type.items())
        ])
        
        # Build milestone list
        milestones = plan.get("milestones", [])
        milestone_list = "\n".join([
            f"- **{m['name']}**: {m['description']}\n  - Required tasks: {len(m['required_tasks'])}\n  - Acceptance: {m['acceptance']}"
            for m in milestones
        ])
        
        # Validation status
        validation = plan.get("validation", {})
        validation_status = "PASSED" if validation_passed else "FAILED"
        validation_errors = ""
        if not validation_passed and validation.get("errors"):
            validation_errors = "\n\nValidation Errors:\n" + "\n".join([
                f"- {error}" for error in validation["errors"]
            ])
        
        report = f"""# Planner Agent Report

## Summary
- Research Bet: **{bet}**
- Strategy: `{strategy}`
- Total Tasks: **{total_tasks}**
- Total Milestones: **{total_milestones}**
- Estimated Time: **{estimated_time_minutes:.1f} minutes**
- Validation Status: **{validation_status}**
- Status: **{result.status}**

## Task Breakdown by Type

| Type | Count |
|------|-------|
{task_breakdown_rows}

## Milestones

{milestone_list if milestone_list else "(No milestones defined)"}

## Plan Details

### Strategy: {strategy}

This plan uses bet-specific decomposition rules to generate tasks:
- Start with small problem sizes (n=2) for fast iteration
- Gradually increase size for exploration
- Multiple random seeds per size for robustness
- Parallel execution possible across different task types

### Task Structure

Each task includes:
- Unique task ID for tracking
- Problem size (n parameter)
- Random seed for determinism
- Acceptance criteria for success validation
- Estimated execution time
- Priority for scheduling

### Validation

{validation_status}{validation_errors}

## Next Steps

1. **Conjecturer Agent** will process these {total_tasks} tasks
   - Generate circuit templates or algorithm schemas
   - Emit Lean stubs and CNF specifications
   - Prepare candidates for mining

2. **Miner Agent** will run SAT solvers on generated instances
   - Use Kissat with fixed seeds
   - Extract patterns from UNSAT proofs
   - Identify counterexamples if SAT

3. **Formalizer Agent** will convert patterns to Lean theorems
   - Apply tactic libraries
   - Reference LRAT proofs by hash
   - Attempt formal verification

4. **Critic Agent** will analyze results for barrier violations
   - Check for relativization
   - Detect natural proofs patterns
   - Suggest non-relativizing modifications

## Configuration

```yaml
bet: {bet}
max_size: {context.config.get('max_size', 'N/A')}
num_seeds: {context.config.get('num_seeds', 'N/A')}
base_seed: {context.seed}
```

---

*Generated by Planner Agent - Rule-based task decomposition for SATurday research*
"""
        
        context.log(self.name, "Report generation complete")
        
        return report
    
    def _generate_yaml_plan(self, context: AgentContext, plan: Dict[str, Any]) -> bool:
        """
        Generate YAML plan file for persistence and human inspection.
        
        Saves plan to search/plans/generated/{run_id}.yaml
        
        Args:
            context: Agent execution context
            plan: Plan dictionary
        
        Returns:
            True if YAML generated successfully, False otherwise
        """
        try:
            # Create generated plans directory if it doesn't exist
            plans_dir = Path("search/plans/generated")
            plans_dir.mkdir(parents=True, exist_ok=True)
            
            # Generate filename with run ID
            yaml_path = plans_dir / f"{context.run_id}.yaml"
            
            # Write plan to YAML
            with open(yaml_path, 'w') as f:
                yaml.dump(plan, f, default_flow_style=False, sort_keys=False)
            
            context.log(self.name, f"YAML plan saved to: {yaml_path}")
            
            return True
        
        except Exception as e:
            context.log(self.name, f"Failed to generate YAML plan: {e}", level="ERROR")
            return False

