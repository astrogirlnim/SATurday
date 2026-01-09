"""
Unit tests for Planner Agent.

Tests cover:
- Bet-specific decomposition (A, B, C, D)
- Task structure and validation
- Milestone generation
- YAML plan generation
- Priority computation
- Size progression
"""

import pytest
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from agents.planner import (
    PlannerAgent,
    BetDecomposer,
    PlanValidator,
    Task,
    Milestone,
)
from agents.core import AgentContext


class TestTask:
    """Test Task dataclass functionality."""
    
    def test_task_creation(self):
        """Test creating a basic task."""
        task = Task(
            task_id="test_task_1",
            bet="A",
            problem_size=5,
            seed=42,
            circuit_type="monotone",
        )
        
        assert task.task_id == "test_task_1"
        assert task.bet == "A"
        assert task.problem_size == 5
        assert task.seed == 42
        assert task.circuit_type == "monotone"
        assert task.timeout_seconds == 300  # default
        assert task.priority == 1  # default
    
    def test_task_to_dict(self):
        """Test task serialization to dictionary."""
        task = Task(
            task_id="test_task_2",
            bet="B",
            problem_size=10,
            seed=100,
            algorithm_schema="sorting",
        )
        
        task_dict = task.to_dict()
        
        assert task_dict["task_id"] == "test_task_2"
        assert task_dict["bet"] == "B"
        assert task_dict["problem_size"] == 10
        assert task_dict["seed"] == 100
        assert task_dict["algorithm_schema"] == "sorting"


class TestBetDecomposer:
    """Test bet-specific decomposition logic."""
    
    def test_decompose_bet_a_basic(self):
        """Test basic Bet A decomposition."""
        decomposer = BetDecomposer()
        
        config = {
            "max_size": 5,
            "num_seeds": 2,
            "circuit_types": ["monotone"],
        }
        
        tasks, milestones = decomposer.decompose_bet_a_circuit_bounds(config, base_seed=42)
        
        # Should have tasks for each size (2-5) with 2 seeds each
        # 4 sizes * 2 seeds * 1 circuit type = 8 tasks
        assert len(tasks) == 8
        assert len(milestones) == 3  # Standard milestones
        
        # Check first task
        first_task = tasks[0]
        assert first_task.bet == "A"
        assert first_task.circuit_type == "monotone"
        assert first_task.problem_size >= 2
    
    def test_decompose_bet_a_multiple_circuit_types(self):
        """Test Bet A with multiple circuit types."""
        decomposer = BetDecomposer()
        
        config = {
            "max_size": 4,
            "num_seeds": 1,
            "circuit_types": ["monotone", "ac0", "formula"],
        }
        
        tasks, milestones = decomposer.decompose_bet_a_circuit_bounds(config, base_seed=100)
        
        # 3 sizes (2, 3, 4) * 1 seed * 3 circuit types = 9 tasks
        assert len(tasks) == 9
        
        # Check circuit type distribution
        monotone_tasks = [t for t in tasks if t.circuit_type == "monotone"]
        ac0_tasks = [t for t in tasks if t.circuit_type == "ac0"]
        formula_tasks = [t for t in tasks if t.circuit_type == "formula"]
        
        assert len(monotone_tasks) == 3
        assert len(ac0_tasks) == 3
        assert len(formula_tasks) == 3
    
    def test_decompose_bet_b_stub(self):
        """Test Bet B decomposition (stub)."""
        decomposer = BetDecomposer()
        
        config = {"max_size": 10, "num_seeds": 3}
        tasks, milestones = decomposer.decompose_bet_b_algorithms(config, base_seed=42)
        
        # Stub should return one placeholder task
        assert len(tasks) == 1
        assert tasks[0].bet == "B"
        assert tasks[0].algorithm_schema == "sorting"
    
    def test_decompose_bet_c_stub(self):
        """Test Bet C decomposition (stub)."""
        decomposer = BetDecomposer()
        
        config = {"max_size": 10}
        tasks, milestones = decomposer.decompose_bet_c_hardness_randomness(config, base_seed=42)
        
        # Stub should return one placeholder task
        assert len(tasks) == 1
        assert tasks[0].bet == "C"
    
    def test_decompose_bet_d_stub(self):
        """Test Bet D decomposition (stub)."""
        decomposer = BetDecomposer()
        
        config = {"max_size": 10}
        tasks, milestones = decomposer.decompose_bet_d_barriers(config, base_seed=42)
        
        # Stub should return one placeholder task
        assert len(tasks) == 1
        assert tasks[0].bet == "D"
    
    def test_size_progression_small_range(self):
        """Test size progression for small max_size."""
        decomposer = BetDecomposer()
        
        sizes = decomposer._generate_size_progression(2, 8)
        
        # For small ranges, should use all values
        assert sizes == [2, 3, 4, 5, 6, 7, 8]
    
    def test_size_progression_large_range(self):
        """Test size progression for large max_size."""
        decomposer = BetDecomposer()
        
        sizes = decomposer._generate_size_progression(2, 50)
        
        # Should have exponential growth
        assert 2 in sizes
        assert 50 in sizes  # max should be included
        assert len(sizes) < 49  # Should skip many intermediate values
    
    def test_estimate_task_time(self):
        """Test task time estimation."""
        decomposer = BetDecomposer()
        
        # Small circuits should be quick
        time_small = decomposer._estimate_task_time(3, "monotone")
        assert time_small < 30
        
        # Large circuits should take longer
        time_large = decomposer._estimate_task_time(15, "ac0")
        assert time_large > time_small
    
    def test_compute_priority(self):
        """Test priority computation."""
        decomposer = BetDecomposer()
        
        # Smaller sizes should have higher priority (lower number)
        priority_small = decomposer._compute_priority(2, "monotone")
        priority_large = decomposer._compute_priority(10, "monotone")
        
        assert priority_small < priority_large
        
        # Monotone should have higher priority than AC0
        priority_monotone = decomposer._compute_priority(5, "monotone")
        priority_ac0 = decomposer._compute_priority(5, "ac0")
        
        assert priority_monotone < priority_ac0


class TestPlanValidator:
    """Test plan validation logic."""
    
    def test_validate_valid_plan(self):
        """Test validation of a valid plan."""
        validator = PlanValidator()
        
        tasks = [
            Task(task_id="task1", bet="A", problem_size=5, seed=42, circuit_type="monotone"),
            Task(task_id="task2", bet="A", problem_size=6, seed=43, circuit_type="ac0"),
        ]
        
        milestones = [
            Milestone(
                name="milestone1",
                description="Test milestone",
                required_tasks=["task1", "task2"],
                acceptance="All tasks complete",
            )
        ]
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert is_valid
        assert len(errors) == 0
    
    def test_validate_empty_plan(self):
        """Test validation fails for empty plan."""
        validator = PlanValidator()
        
        tasks = []
        milestones = []
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert not is_valid
        assert "no tasks" in errors[0].lower()
    
    def test_validate_duplicate_task_ids(self):
        """Test validation catches duplicate task IDs."""
        validator = PlanValidator()
        
        tasks = [
            Task(task_id="duplicate", bet="A", problem_size=5, seed=42),
            Task(task_id="duplicate", bet="A", problem_size=6, seed=43),
        ]
        
        milestones = []
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert not is_valid
        assert any("duplicate" in e.lower() for e in errors)
    
    def test_validate_invalid_parameters(self):
        """Test validation catches invalid task parameters."""
        validator = PlanValidator()
        
        tasks = [
            Task(task_id="invalid1", bet="A", problem_size=-1, seed=42),  # Invalid size
            Task(task_id="invalid2", bet="X", problem_size=5, seed=43),   # Invalid bet
        ]
        
        milestones = []
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert not is_valid
        assert len(errors) >= 2
    
    def test_validate_invalid_dependency(self):
        """Test validation catches invalid task dependencies."""
        validator = PlanValidator()
        
        tasks = [
            Task(
                task_id="task1",
                bet="A",
                problem_size=5,
                seed=42,
                dependencies=["nonexistent_task"],
            ),
        ]
        
        milestones = []
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert not is_valid
        assert any("invalid dependency" in e.lower() for e in errors)
    
    def test_validate_circular_dependency(self):
        """Test validation catches circular dependencies (self-loops)."""
        validator = PlanValidator()
        
        tasks = [
            Task(
                task_id="task1",
                bet="A",
                problem_size=5,
                seed=42,
                dependencies=["task1"],  # Self-loop
            ),
        ]
        
        milestones = []
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert not is_valid
        assert any("circular" in e.lower() for e in errors)
    
    def test_validate_milestone_invalid_task(self):
        """Test validation catches milestones referencing invalid tasks."""
        validator = PlanValidator()
        
        tasks = [
            Task(task_id="task1", bet="A", problem_size=5, seed=42),
        ]
        
        milestones = [
            Milestone(
                name="milestone1",
                description="Test",
                required_tasks=["task1", "nonexistent"],
                acceptance="Test",
            )
        ]
        
        is_valid, errors = validator.validate(tasks, milestones)
        
        assert not is_valid
        assert any("invalid task" in e.lower() for e in errors)


class TestPlannerAgent:
    """Test PlannerAgent integration."""
    
    def test_planner_agent_creation(self):
        """Test creating a planner agent."""
        planner = PlannerAgent()
        
        assert planner.name == "planner"
        assert isinstance(planner.decomposer, BetDecomposer)
        assert isinstance(planner.validator, PlanValidator)
    
    def test_plan_phase_bet_a(self):
        """Test planning phase for Bet A."""
        planner = PlannerAgent()
        
        context = AgentContext(
            run_id="test_run_123",
            seed=42,
            timestamp="2026-01-09T12:00:00",
            config={
                "bet": "A",
                "max_size": 4,
                "num_seeds": 2,
                "circuit_types": ["monotone"],
            },
        )
        
        plan = planner.plan(context)
        
        assert plan["bet"] == "A"
        assert plan["strategy"] == "circuit_lower_bounds"
        assert plan["total_tasks"] > 0
        assert plan["total_milestones"] > 0
        assert "tasks" in plan
        assert "milestones" in plan
        assert "validation" in plan
    
    def test_plan_phase_bet_b(self):
        """Test planning phase for Bet B (stub)."""
        planner = PlannerAgent()
        
        context = AgentContext(
            run_id="test_run_124",
            seed=100,
            timestamp="2026-01-09T12:00:00",
            config={"bet": "B", "max_size": 10},
        )
        
        plan = planner.plan(context)
        
        assert plan["bet"] == "B"
        assert plan["strategy"] == "algorithm_synthesis"
        assert plan["total_tasks"] == 1  # Stub
    
    def test_act_phase(self):
        """Test acting phase."""
        planner = PlannerAgent()
        
        context = AgentContext(
            run_id="test_run_125",
            seed=42,
            timestamp="2026-01-09T12:00:00",
            config={"bet": "A", "max_size": 3, "num_seeds": 1},
        )
        
        # First, plan
        plan = planner.plan(context)
        
        # Then, act
        result = planner.act(context, plan)
        
        assert result.status == "success"
        assert result.agent_name == "planner"
        assert "plan" in result.artifacts
        assert result.metrics["total_tasks"] > 0
    
    def test_report_phase(self):
        """Test reporting phase."""
        planner = PlannerAgent()
        
        context = AgentContext(
            run_id="test_run_126",
            seed=42,
            timestamp="2026-01-09T12:00:00",
            config={"bet": "A", "max_size": 3, "num_seeds": 1},
        )
        
        # Plan, act, then report
        plan = planner.plan(context)
        result = planner.act(context, plan)
        report = planner.report(context, result)
        
        assert "Planner Agent Report" in report
        assert "Summary" in report
        assert "Task Breakdown" in report
        assert "Milestones" in report
        assert "Next Steps" in report
    
    def test_execute_full_lifecycle(self):
        """Test full agent execution lifecycle."""
        planner = PlannerAgent()
        
        context = AgentContext(
            run_id="test_run_127",
            seed=42,
            timestamp="2026-01-09T12:00:00",
            config={"bet": "A", "max_size": 4, "num_seeds": 1},
        )
        
        # Execute full lifecycle
        result = planner.execute(context)
        
        assert result.status == "success"
        assert result.duration_seconds > 0
        assert "plan" in result.artifacts
        assert "report" in result.artifacts
        assert result.metrics["total_tasks"] > 0
    
    def test_unknown_bet_fallback(self):
        """Test handling of unknown bet with fallback to Bet A."""
        planner = PlannerAgent()
        
        context = AgentContext(
            run_id="test_run_128",
            seed=42,
            timestamp="2026-01-09T12:00:00",
            config={"bet": "Z", "max_size": 3, "num_seeds": 1},  # Invalid bet
        )
        
        plan = planner.plan(context)
        
        # Should fallback to Bet A
        assert plan["bet"] == "Z"  # Preserves original bet in plan
        assert plan["strategy"] == "circuit_lower_bounds_fallback"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])

