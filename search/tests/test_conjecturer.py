"""
Unit tests for Conjecturer Agent and template system.

Tests cover:
- Template base classes
- Bet A circuit templates
- Conjecture instantiation
- File generation (Lean stubs, CNF specs)
- Agent integration
"""

import pytest
import tempfile
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from templates.base import ConjectureTemplate, Conjecture, TemplateRegistry
from templates.bet_a_circuits import (
    MonotoneParityTemplate,
    MonotoneMajorityTemplate,
    AC0ParityTemplate,
    AC0MajorityTemplate,
    FormulaParityTemplate,
)
from agents.conjecturer import ConjecturerAgent
from agents.core import AgentContext


class TestConjecture:
    """Test Conjecture dataclass functionality."""
    
    def test_conjecture_creation(self):
        """Test creating a basic conjecture."""
        conj = Conjecture(
            conjecture_id="test_conj_1",
            task_id="task_1",
            bet="A",
            lean_stub="theorem test : True := sorry",
            cnf_spec={"type": "test"},
        )
        
        assert conj.conjecture_id == "test_conj_1"
        assert conj.task_id == "task_1"
        assert conj.bet == "A"
        assert "theorem test" in conj.lean_stub
        assert conj.cnf_spec["type"] == "test"
    
    def test_conjecture_to_dict(self):
        """Test conjecture serialization."""
        conj = Conjecture(
            conjecture_id="test_conj_2",
            task_id="task_2",
            bet="A",
            lean_stub="theorem test : True := sorry",
            cnf_spec={"type": "test"},
        )
        
        conj_dict = conj.to_dict()
        
        assert conj_dict["conjecture_id"] == "test_conj_2"
        assert conj_dict["task_id"] == "task_2"
        assert conj_dict["bet"] == "A"
        assert "theorem test" in conj_dict["lean_stub_preview"]
    
    def test_write_lean_stub(self):
        """Test writing Lean stub to file."""
        conj = Conjecture(
            conjecture_id="test_conj_3",
            task_id="task_3",
            bet="A",
            lean_stub="import Mathlib\n\ntheorem test : True := sorry",
            cnf_spec={},
        )
        
        with tempfile.TemporaryDirectory() as tmpdir:
            base_dir = Path(tmpdir)
            file_path = conj.write_lean_stub(base_dir)
            
            assert file_path.exists()
            assert file_path.name == "test_conj_3.lean"
            assert "BetA" in str(file_path)
            
            content = file_path.read_text()
            assert "theorem test" in content
    
    def test_write_cnf_spec(self):
        """Test writing CNF spec to YAML file."""
        conj = Conjecture(
            conjecture_id="test_conj_4",
            task_id="task_4",
            bet="A",
            lean_stub="",
            cnf_spec={
                "circuit": {"type": "monotone", "num_inputs": 5},
                "target_function": "parity",
            },
        )
        
        with tempfile.TemporaryDirectory() as tmpdir:
            base_dir = Path(tmpdir)
            file_path = conj.write_cnf_spec(base_dir)
            
            assert file_path.exists()
            assert file_path.name == "test_conj_4.yaml"
            
            import yaml
            with open(file_path) as f:
                spec = yaml.safe_load(f)
            
            assert spec["circuit"]["type"] == "monotone"
            assert spec["target_function"] == "parity"


class TestTemplateRegistry:
    """Test template registry functionality."""
    
    def test_registry_creation(self):
        """Test creating a registry."""
        registry = TemplateRegistry()
        assert len(registry.get_all_templates()) == 0
    
    def test_register_template(self):
        """Test registering a template."""
        registry = TemplateRegistry()
        template = MonotoneParityTemplate()
        
        registry.register("A", "monotone", template)
        
        templates = registry.get_templates("A", "monotone")
        assert len(templates) == 1
        assert templates[0] == template
    
    def test_get_nonexistent_templates(self):
        """Test getting templates that don't exist."""
        registry = TemplateRegistry()
        
        templates = registry.get_templates("Z", "unknown")
        assert len(templates) == 0


class TestMonotoneParityTemplate:
    """Test MonotoneParityTemplate."""
    
    def test_template_creation(self):
        """Test creating template."""
        template = MonotoneParityTemplate()
        assert template.template_id == "monotone_parity"
        assert template.bet == "A"
    
    def test_generate_lean_stub(self):
        """Test Lean stub generation."""
        template = MonotoneParityTemplate()
        
        lean_stub = template.generate_lean_stub(n=3, seed=42, task_id="test_task")
        
        assert "parity_3" in lean_stub
        assert "monotone_parity_lower_bound_3_s42" in lean_stub
        assert "sorry" in lean_stub
        assert "import Mathlib" in lean_stub
        assert "namespace SATurday" in lean_stub
    
    def test_generate_cnf_spec(self):
        """Test CNF spec generation."""
        template = MonotoneParityTemplate()
        
        spec = template.generate_cnf_spec(n=3, seed=42, task_id="test_task")
        
        assert spec["circuit"]["type"] == "monotone"
        assert spec["circuit"]["num_inputs"] == 3
        assert spec["target_function"]["name"] == "parity"
        assert spec["seed"] == 42
    
    def test_instantiate_with_task(self):
        """Test template instantiation with task."""
        template = MonotoneParityTemplate()
        
        task = {
            "task_id": "bet_a_monotone_n4_s100",
            "problem_size": 4,
            "seed": 100,
            "circuit_type": "monotone",
        }
        
        conjecture = template.instantiate(task)
        
        assert conjecture.conjecture_id == "monotone_parity_n4_s100"
        assert conjecture.task_id == "bet_a_monotone_n4_s100"
        assert conjecture.bet == "A"
        assert "parity_4" in conjecture.lean_stub
        assert conjecture.cnf_spec["circuit"]["num_inputs"] == 4


class TestOtherBetATemplates:
    """Test other Bet A templates."""
    
    def test_monotone_majority_template(self):
        """Test MonotoneMajorityTemplate."""
        template = MonotoneMajorityTemplate()
        
        lean_stub = template.generate_lean_stub(n=5, seed=1, task_id="test")
        spec = template.generate_cnf_spec(n=5, seed=1, task_id="test")
        
        assert "majority_5" in lean_stub
        assert spec["target_function"]["name"] == "majority"
    
    def test_ac0_parity_template(self):
        """Test AC0ParityTemplate."""
        template = AC0ParityTemplate()
        
        lean_stub = template.generate_lean_stub(n=4, seed=2, task_id="test")
        spec = template.generate_cnf_spec(n=4, seed=2, task_id="test")
        
        assert "AC0Circuit" in lean_stub
        assert spec["circuit"]["type"] == "ac0"
        assert "max_depth" in spec["circuit"]
    
    def test_ac0_majority_template(self):
        """Test AC0MajorityTemplate."""
        template = AC0MajorityTemplate()
        
        lean_stub = template.generate_lean_stub(n=3, seed=3, task_id="test")
        spec = template.generate_cnf_spec(n=3, seed=3, task_id="test")
        
        assert "AC0Circuit" in lean_stub
        assert spec["target_function"]["name"] == "majority"
    
    def test_formula_parity_template(self):
        """Test FormulaParityTemplate."""
        template = FormulaParityTemplate()
        
        lean_stub = template.generate_lean_stub(n=3, seed=4, task_id="test")
        spec = template.generate_cnf_spec(n=3, seed=4, task_id="test")
        
        assert "FormulaCircuit" in lean_stub
        assert spec["circuit"]["type"] == "formula"
        assert "fan_out_limit" in spec["circuit"]


class TestConjecturerAgent:
    """Test ConjecturerAgent integration."""
    
    def test_agent_creation(self):
        """Test creating conjecturer agent."""
        agent = ConjecturerAgent()
        
        assert agent.name == "conjecturer"
        assert agent.registry is not None
        assert len(agent.registry.get_all_templates()) > 0
    
    def test_template_registration(self):
        """Test that templates are registered."""
        agent = ConjecturerAgent()
        
        # Check monotone templates
        monotone_templates = agent.registry.get_templates("A", "monotone")
        assert len(monotone_templates) >= 2  # parity and majority
        
        # Check AC0 templates
        ac0_templates = agent.registry.get_templates("A", "ac0")
        assert len(ac0_templates) >= 2
        
        # Check formula templates
        formula_templates = agent.registry.get_templates("A", "formula")
        assert len(formula_templates) >= 1
    
    def test_plan_phase(self):
        """Test planning phase."""
        agent = ConjecturerAgent()
        
        # Create context with planner artifacts
        context = AgentContext(
            run_id="test_run",
            seed=42,
            timestamp="2026-01-10T00:00:00",
            config={"max_conjectures": 5},
            artifacts={
                "planner": {
                    "plan": {
                        "tasks": [
                            {
                                "task_id": "bet_a_monotone_n2_s42",
                                "bet": "A",
                                "problem_size": 2,
                                "seed": 42,
                                "circuit_type": "monotone",
                            },
                            {
                                "task_id": "bet_a_ac0_n3_s43",
                                "bet": "A",
                                "problem_size": 3,
                                "seed": 43,
                                "circuit_type": "ac0",
                            },
                        ]
                    }
                }
            },
        )
        
        plan = agent.plan(context)
        
        assert plan["mode"] == "template"
        assert plan["num_tasks"] == 2
        assert "output_dirs" in plan
    
    def test_act_phase(self):
        """Test acting phase."""
        agent = ConjecturerAgent()
        
        # Create context
        context = AgentContext(
            run_id="test_run",
            seed=42,
            timestamp="2026-01-10T00:00:00",
            config={},
        )
        
        # Create plan with sample tasks
        with tempfile.TemporaryDirectory() as tmpdir:
            plan = {
                "tasks": [
                    {
                        "task_id": "bet_a_monotone_n2_s42",
                        "bet": "A",
                        "problem_size": 2,
                        "seed": 42,
                        "circuit_type": "monotone",
                    },
                ],
                "num_tasks": 1,
                "mode": "template",
                "output_dirs": {
                    "lean": str(Path(tmpdir) / "lean"),
                    "specs": str(Path(tmpdir) / "specs"),
                },
            }
            
            result = agent.act(context, plan)
            
            assert result.status == "success"
            assert result.metrics["num_generated"] >= 1
            assert len(result.artifacts["conjectures"]) >= 1
            
            # Check files were created
            lean_dir = Path(tmpdir) / "lean"
            spec_dir = Path(tmpdir) / "specs"
            
            # Should have created at least one Lean file
            lean_files = list(lean_dir.rglob("*.lean"))
            assert len(lean_files) >= 1
            
            # Should have created at least one spec file
            spec_files = list(spec_dir.glob("*.yaml"))
            assert len(spec_files) >= 1
    
    def test_execute_full_lifecycle(self):
        """Test full agent execution lifecycle."""
        agent = ConjecturerAgent()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            context = AgentContext(
                run_id="test_run",
                seed=42,
                timestamp="2026-01-10T00:00:00",
                config={"max_conjectures": 3},
                artifacts={
                    "planner": {
                        "plan": {
                            "tasks": [
                                {
                                    "task_id": "bet_a_formula_n2_s42",
                                    "bet": "A",
                                    "problem_size": 2,
                                    "seed": 42,
                                    "circuit_type": "formula",
                                },
                            ]
                        }
                    }
                },
            )
            
            # Override output dirs for test
            original_parent = Path(__file__).parent.parent.parent
            test_parent = Path(tmpdir)
            
            # Execute full lifecycle
            result = agent.execute(context)
            
            assert result.status == "success"
            assert result.duration_seconds > 0
            assert "conjectures" in result.artifacts
            assert "report" in result.artifacts


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
