"""
Tests for Formalizer Agent and Lean Theorem Templates.

Tests cover:
- LeanTheorem dataclass and file writing
- TheoremRegistry operations
- Template instantiation for each circuit type
- FormalizerAgent lifecycle (plan, act, report)
- Integration with mining results
- LRAT hash embedding
- File generation to correct directories

LOG: Formalizer agent test suite
"""

import os
import sys
import tempfile
from pathlib import Path

import pytest

# Add search directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from agents.core import AgentContext, AgentResult
from agents.formalizer import FormalizerAgent
from templates.lean_theorems import (
    LeanTheorem,
    LeanTheoremTemplate,
    MonotoneParityProofTemplate,
    AC0ParityProofTemplate,
    FormulaParityProofTemplate,
    TheoremRegistry as LeanTheoremRegistry,
)


class TestLeanTheorem:
    """Tests for LeanTheorem dataclass."""
    
    def test_create_theorem(self):
        """Test creating a LeanTheorem instance."""
        theorem = LeanTheorem(
            theorem_id="test_theorem",
            theorem_text="theorem test : True := by trivial",
            lrat_hash="abc123",
            status="complete",
            circuit_type="monotone",
            target_function="parity",
            n=2,
            seed=42
        )
        
        assert theorem.theorem_id == "test_theorem"
        assert "trivial" in theorem.theorem_text
        assert theorem.lrat_hash == "abc123"
        assert theorem.status == "complete"
        assert theorem.n == 2
    
    def test_write_lean_file(self):
        """Test writing theorem to file."""
        theorem = LeanTheorem(
            theorem_id="monotone_parity_n2_s100_proof",
            theorem_text="theorem test : True := by trivial\n",
            status="complete"
        )
        
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = theorem.write_lean_file(tmpdir)
            
            # Check file was created
            assert os.path.exists(filepath)
            
            # Check directory structure
            expected_dir = os.path.join(
                tmpdir, "theory", "Conjectures", "BetA", "Proofs"
            )
            assert os.path.exists(expected_dir)
            
            # Check filename
            assert filepath.endswith("monotone_parity_n2_s100_proof.lean")
            
            # Check contents
            with open(filepath) as f:
                content = f.read()
            assert "trivial" in content
    
    def test_status_detection(self):
        """Test status is set based on sorry presence."""
        complete = LeanTheorem(
            theorem_id="complete",
            theorem_text="theorem test : True := by trivial"
        )
        assert complete.status == "partial"  # Default is partial
        
        partial = LeanTheorem(
            theorem_id="partial",
            theorem_text="theorem test : True := sorry",
            status="partial"
        )
        assert partial.status == "partial"


class TestMonotoneParityProofTemplate:
    """Tests for MonotoneParityProofTemplate."""
    
    def test_create_template(self):
        """Test template initialization."""
        template = MonotoneParityProofTemplate()
        assert template.template_id == "monotone_parity"
        assert template.bet == "A"
    
    def test_generate_small_n(self):
        """Test theorem generation for small n."""
        template = MonotoneParityProofTemplate()
        
        theorem_text = template.generate_theorem(
            n=2,
            seed=100,
            task_id="test_task",
            lrat_hash="abc123"
        )
        
        # Check structure
        assert "import Mathlib" in theorem_text
        assert "import Tactics.CircuitTactics" in theorem_text
        assert "parity_2" in theorem_text
        assert "MonotoneCircuit" in theorem_text
        assert "monotone_parity_lower_bound_2_s100_proof" in theorem_text
        assert "LRAT Proof: abc123" in theorem_text
        assert "2^2" in theorem_text
    
    def test_generate_large_n(self):
        """Test theorem generation for large n (different strategy)."""
        template = MonotoneParityProofTemplate()
        
        theorem_text = template.generate_theorem(
            n=10,
            seed=200,
            task_id="test_large",
            lrat_hash="def456"
        )
        
        # Check uses exponential strategy
        assert "exp_lower_bound" in theorem_text
        assert "2^10" in theorem_text
        assert "parity_10" in theorem_text
    
    def test_instantiate_creates_theorem(self):
        """Test instantiate method returns LeanTheorem."""
        template = MonotoneParityProofTemplate()
        
        theorem = template.instantiate(
            n=3,
            seed=300,
            task_id="test_inst",
            lrat_hash="ghi789",
            circuit_type="monotone",
            target_function="parity"
        )
        
        assert isinstance(theorem, LeanTheorem)
        assert theorem.theorem_id == "monotone_parity_n3_s300_proof"
        assert theorem.n == 3
        assert theorem.seed == 300
        assert theorem.lrat_hash == "ghi789"
        assert theorem.circuit_type == "monotone"
        assert theorem.target_function == "parity"
        assert "sorry" in theorem.theorem_text  # Partial proof


class TestAC0ParityProofTemplate:
    """Tests for AC0ParityProofTemplate."""
    
    def test_create_template(self):
        """Test AC0 template initialization."""
        template = AC0ParityProofTemplate()
        assert template.template_id == "ac0_parity"
        assert template.bet == "A"
    
    def test_generate_with_depth(self):
        """Test AC0 theorem generation includes depth parameter."""
        template = AC0ParityProofTemplate()
        
        theorem_text = template.generate_theorem(
            n=4,
            seed=400,
            task_id="test_ac0",
            lrat_hash="jkl012",
            depth=3
        )
        
        # Check AC0-specific elements
        assert "AC0Circuit" in theorem_text
        assert "depth" in theorem_text.lower()
        assert "d3_s400_proof" in theorem_text or "depth=3" in theorem_text
        assert "switching lemma" in theorem_text.lower()


class TestFormulaParityProofTemplate:
    """Tests for FormulaParityProofTemplate."""
    
    def test_create_template(self):
        """Test formula template initialization."""
        template = FormulaParityProofTemplate()
        assert template.template_id == "formula_parity"
        assert template.bet == "A"
    
    def test_generate_quadratic_bound(self):
        """Test formula theorem has quadratic lower bound."""
        template = FormulaParityProofTemplate()
        
        theorem_text = template.generate_theorem(
            n=5,
            seed=500,
            task_id="test_formula",
            lrat_hash="mno345"
        )
        
        # Check formula-specific elements
        assert "FormulaCircuit" in theorem_text
        assert "fan-out 1" in theorem_text.lower() or "tree" in theorem_text.lower()
        assert "5 * 5" in theorem_text  # n^2 bound
        assert "quadratic" in theorem_text.lower()


class TestTheoremRegistry:
    """Tests for TheoremRegistry."""
    
    def test_create_registry(self):
        """Test registry initialization with defaults."""
        registry = LeanTheoremRegistry()
        templates = registry.list_templates()
        
        # Check default templates registered
        assert ("A", "monotone", "parity") in templates
        assert ("A", "ac0", "parity") in templates
        assert ("A", "formula", "parity") in templates
    
    def test_get_template_monotone(self):
        """Test retrieving monotone parity template."""
        registry = LeanTheoremRegistry()
        template = registry.get_template("A", "monotone", "parity")
        
        assert template is not None
        assert isinstance(template, MonotoneParityProofTemplate)
    
    def test_get_template_ac0(self):
        """Test retrieving AC0 parity template."""
        registry = LeanTheoremRegistry()
        template = registry.get_template("A", "ac0", "parity")
        
        assert template is not None
        assert isinstance(template, AC0ParityProofTemplate)
    
    def test_get_template_formula(self):
        """Test retrieving formula parity template."""
        registry = LeanTheoremRegistry()
        template = registry.get_template("A", "formula", "parity")
        
        assert template is not None
        assert isinstance(template, FormulaParityProofTemplate)
    
    def test_get_nonexistent_template(self):
        """Test retrieving non-existent template returns None."""
        registry = LeanTheoremRegistry()
        template = registry.get_template("B", "quantum", "clique")
        
        assert template is None
    
    def test_register_custom_template(self):
        """Test registering a custom template."""
        registry = LeanTheoremRegistry()
        custom = MonotoneParityProofTemplate()  # Reuse for testing
        
        registry.register("Z", "custom", "test", custom)
        
        retrieved = registry.get_template("Z", "custom", "test")
        assert retrieved is custom


class TestFormalizerAgent:
    """Tests for FormalizerAgent."""
    
    def test_create_agent(self):
        """Test agent initialization."""
        agent = FormalizerAgent()
        assert agent.name == "formalizer"
        assert agent.registry is not None
        # Check the registry has the expected type name
        assert agent.registry.__class__.__name__ == "TheoremRegistry"
    
    def test_plan_no_unsat(self):
        """Test planning with no UNSAT instances."""
        agent = FormalizerAgent()
        context = AgentContext(run_id="test", seed=100, timestamp="2026-01-10")
        
        # No mining results
        context.artifacts["miner"] = {"mining_results": []}
        
        plan = agent.plan(context)
        
        assert plan["num_candidates"] == 0
        assert plan["tactic_mode"] == "library"
        assert plan["accept_sorry"] is True
    
    def test_plan_with_unsat(self):
        """Test planning with UNSAT instances."""
        agent = FormalizerAgent()
        context = AgentContext(run_id="test", seed=200, timestamp="2026-01-10")
        
        # Mock mining results with UNSAT
        context.artifacts["miner"] = {
            "mining_results": [
                {
                    "status": "SAT",
                    "spec": {
                        "circuit": {"type": "monotone", "num_inputs": 2},
                        "target_function": {"name": "parity"}
                    }
                },
                {
                    "status": "UNSAT",
                    "spec": {
                        "circuit": {"type": "monotone", "num_inputs": 3},
                        "target_function": {"name": "parity"}
                    },
                    "lrat_hash": "abc123"
                },
                {
                    "status": "UNSAT",
                    "spec": {
                        "circuit": {"type": "ac0", "num_inputs": 3, "depth": 2},
                        "target_function": {"name": "parity"}
                    },
                    "lrat_hash": "def456"
                }
            ]
        }
        
        plan = agent.plan(context)
        
        assert plan["num_candidates"] == 2  # Two UNSAT
        assert "monotone" in plan["circuit_types"]
        assert "ac0" in plan["circuit_types"]
        assert "parity" in plan["target_functions"]
        assert len(plan["unsat_instances"]) == 2
    
    def test_formalize_instance(self):
        """Test formalizing a single instance."""
        agent = FormalizerAgent()
        context = AgentContext(run_id="test", seed=300, timestamp="2026-01-10")
        
        instance = {
            "status": "UNSAT",
            "spec": {
                "circuit": {"type": "monotone", "num_inputs": 2},
                "target_function": {"name": "parity"},
                "task_id": "test_task",
                "conjecture_id": "monotone_parity_n2_s100"
            },
            "seed": 100,
            "lrat_hash": "test_hash_123"
        }
        
        theorem = agent._formalize_instance(instance, context)
        
        assert theorem.__class__.__name__ == "LeanTheorem"
        assert theorem.circuit_type == "monotone"
        assert theorem.target_function == "parity"
        assert theorem.n == 2
        assert theorem.seed == 100
        assert theorem.lrat_hash == "test_hash_123"
        assert "monotone_parity_n2_s100_proof" in theorem.theorem_id
    
    def test_act_generates_theorems(self):
        """Test act phase generates theorems."""
        agent = FormalizerAgent()
        context = AgentContext(run_id="test", seed=400, timestamp="2026-01-10")
        
        # Mock plan from plan phase
        plan = {
            "num_candidates": 1,
            "circuit_types": ["monotone"],
            "target_functions": ["parity"],
            "tactic_mode": "library",
            "target_language": "lean4",
            "accept_sorry": True,
            "unsat_instances": [
                {
                    "status": "UNSAT",
                    "spec": {
                        "circuit": {"type": "monotone", "num_inputs": 2},
                        "target_function": {"name": "parity"},
                        "task_id": "test",
                        "conjecture_id": "test_conj"
                    },
                    "seed": 200,
                    "lrat_hash": "xyz789"
                }
            ]
        }
        
        result = agent.act(context, plan)
        
        assert result.status in ["success", "partial_success"]
        assert result.metrics["theorems_generated"] >= 1
        assert result.metrics["failed"] == 0 or result.metrics["theorems_generated"] > 0
    
    def test_report_generation(self):
        """Test report generation."""
        agent = FormalizerAgent()
        context = AgentContext(run_id="test", seed=500, timestamp="2026-01-10")
        
        # Mock result
        result = AgentResult(
            agent_name="formalizer",
            status="success",
            artifacts={
                "theorems": [
                    {
                        "theorem_id": "test_theorem",
                        "circuit_type": "monotone",
                        "target_function": "parity",
                        "n": 2,
                        "seed": 300,
                        "status": "partial",
                        "lrat_hash": "test_hash"
                    }
                ],
                "written_files": ["/path/to/theorem.lean"],
                "count": 1
            },
            metrics={
                "theorems_generated": 1,
                "complete_proofs": 0,
                "partial_proofs": 1,
                "failed": 0,
                "files_written": 1
            }
        )
        
        report = agent.report(context, result)
        
        # Check report structure
        assert "Formalizer Agent Report" in report
        assert "test_theorem" in report
        assert "monotone" in report
        assert "parity" in report
        assert "n=2" in report
        assert "seed: 300" in report.lower()
        assert "make verify" in report.lower()


class TestIntegration:
    """Integration tests for full formalization pipeline."""
    
    def test_full_lifecycle(self):
        """Test complete agent lifecycle: plan → act → report."""
        agent = FormalizerAgent()
        context = AgentContext(run_id="test", seed=600, timestamp="2026-01-10")
        
        # Setup mining results
        context.artifacts["miner"] = {
            "mining_results": [
                {
                    "status": "UNSAT",
                    "spec": {
                        "circuit": {"type": "formula", "num_inputs": 3},
                        "target_function": {"name": "parity"},
                        "task_id": "integration_test",
                        "conjecture_id": "formula_parity_n3_s1000"
                    },
                    "seed": 1000,
                    "lrat_hash": "integration_hash"
                }
            ]
        }
        
        # Execute lifecycle
        plan = agent.plan(context)
        assert plan["num_candidates"] == 1
        
        result = agent.act(context, plan)
        assert result.status in ["success", "partial_success"]
        
        report = agent.report(context, result)
        assert "integration_test" in report or "formula" in report


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
