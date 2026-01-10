"""
Unit tests for Proof Critic Agent.

Tests cover:
- ProofParser: Lean file parsing
- BarrierDetector: Relativization, natural proofs, oracle diagnostics
- CriticAgent: Full agent lifecycle
"""

import tempfile
from pathlib import Path
from typing import Dict, Any
import pytest

from search.agents.critic import (
    ProofParser,
    BarrierDetector,
    CriticAgent,
    ProofAnalysis,
)
from search.agents.core import AgentContext, AgentResult


# === Test Fixtures ===

@pytest.fixture
def sample_lean_monotone_parity():
    """Sample Lean theorem for monotone parity lower bound."""
    return """
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic

namespace SATurday.Conjectures.BetA

/-- Parity function on 2 inputs for monotone circuits -/
def parity_2 (inputs : Fin 2 → Bool) : Bool :=
  sorry

theorem monotone_parity_lower_bound_2_s12000 :
  ∀ (C : MonotoneCircuit),
    C.num_inputs = 2 →
    C.computes (parity_2) →
    C.size ≥ 2^2 := by
  intro C h_inputs h_computes
  induction C.size with
  | zero => sorry
  | succ n ih => sorry

end SATurday.Conjectures.BetA
"""


@pytest.fixture
def sample_lean_with_oracle():
    """Sample Lean theorem using oracle operations."""
    return """
import Mathlib.Data.Bool.Basic

namespace SATurday.Conjectures.BetA

/-- Theorem using oracle queries -/
theorem oracle_based_lower_bound :
  ∀ (C : CircuitWithOracle) (oracle : Oracle),
    C.queries_oracle oracle →
    C.size ≥ 100 := by
  intro C oracle h_oracle
  apply oracle_lower_bound_lemma
  exact h_oracle

end SATurday.Conjectures.BetA
"""


@pytest.fixture
def sample_lean_natural_proof():
    """Sample Lean theorem with natural proof characteristics."""
    return """
import Mathlib.Data.Bool.Basic

namespace SATurday.Conjectures.BetA

/-- Natural proof example: broad + constructive -/
theorem natural_proof_example :
  ∀ (C : MonotoneCircuit) (f : BoolFunction),
    (∀ g, g.is_monotone → count_gates g ≤ C.size) →
    C.computes f →
    C.size ≥ 2^n := by
  intro C f h_count h_computes
  -- Explicit counting argument
  have h_cardinality : cardinality MonotoneCircuits = 2^(2^n) := by sorry
  simp [h_count]
  omega

end SATurday.Conjectures.BetA
"""


@pytest.fixture
def parser():
    """Create ProofParser instance."""
    return ProofParser()


@pytest.fixture
def detector():
    """Create BarrierDetector instance."""
    return BarrierDetector()


@pytest.fixture
def agent_context():
    """Create sample AgentContext."""
    return AgentContext(
        run_id="test_run",
        seed=42,
        timestamp="2026-01-10T12:00:00",
        config={},
        artifacts={
            "formalizer": {
                "theorem_files": [],
            },
            "conjecturer": {
                "conjectures": [],
            },
        },
    )


# === ProofParser Tests ===

def test_parser_extracts_theorem_name(parser, sample_lean_monotone_parity, tmp_path):
    """Test parser extracts theorem name from Lean file."""
    # Create temp file
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    # Parse
    result = parser.parse_lean_file(lean_file)
    
    # Verify
    assert result["theorem_name"] == "monotone_parity_lower_bound_2_s12000"


def test_parser_extracts_tactics(parser, sample_lean_monotone_parity, tmp_path):
    """Test parser extracts tactics used in proof."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    result = parser.parse_lean_file(lean_file)
    
    assert "intro" in result["tactics"]
    assert "induction" in result["tactics"]


def test_parser_detects_sorry(parser, sample_lean_monotone_parity, tmp_path):
    """Test parser detects sorry placeholder."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    result = parser.parse_lean_file(lean_file)
    
    assert result["has_sorry"] is True


def test_parser_extracts_circuit_properties(parser, sample_lean_monotone_parity, tmp_path):
    """Test parser extracts circuit-specific keywords."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    result = parser.parse_lean_file(lean_file)
    
    # Should extract circuit-related keywords from the file
    assert "monotone" in result["circuit_properties"]
    assert "parity" in result["circuit_properties"]
    assert "size" in result["circuit_properties"]


def test_parser_extracts_imports(parser, sample_lean_monotone_parity, tmp_path):
    """Test parser extracts import statements."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    result = parser.parse_lean_file(lean_file)
    
    assert "Mathlib.Data.Bool.Basic" in result["imports"]
    assert "Mathlib.Data.Fin.Basic" in result["imports"]


def test_parser_handles_missing_file(parser, tmp_path):
    """Test parser handles missing files gracefully."""
    lean_file = tmp_path / "nonexistent.lean"
    
    result = parser.parse_lean_file(lean_file)
    
    assert result["theorem_name"] == "unknown"
    assert result["has_sorry"] is True


def test_parser_extracts_lemmas(parser, sample_lean_with_oracle, tmp_path):
    """Test parser extracts lemma references."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_with_oracle)
    
    result = parser.parse_lean_file(lean_file)
    
    assert "oracle_lower_bound_lemma" in result["lemmas_used"]


# === BarrierDetector Tests ===

def test_relativization_detector_basic(detector, parser, sample_lean_monotone_parity, tmp_path):
    """Test relativization detector on basic proof."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.check_relativization(proof_data)
    
    assert "relativizes" in result
    assert "confidence" in result
    assert "evidence" in result
    assert "suggestions" in result
    assert 0.0 <= result["confidence"] <= 1.0


def test_relativization_detector_with_oracle(detector, parser, sample_lean_with_oracle, tmp_path):
    """Test relativization detector identifies oracle usage."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_with_oracle)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.check_relativization(proof_data)
    
    # Oracle usage is a non-relativizing signal
    assert "oracle" in result["evidence"][0].lower() or "blackbox" in result["evidence"][0].lower()


def test_natural_proofs_detector_basic(detector, parser, sample_lean_monotone_parity, tmp_path):
    """Test natural proof detector on basic proof."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.check_natural_proofs(proof_data, "monotone")
    
    assert "is_natural_proof" in result
    assert "largeness_score" in result
    assert "constructivity_score" in result
    assert "evidence" in result


def test_natural_proofs_detector_catches_largeness(detector, parser, sample_lean_natural_proof, tmp_path):
    """Test natural proof detector identifies largeness."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_natural_proof)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.check_natural_proofs(proof_data, "monotone")
    
    # Should detect largeness (forall over all circuits)
    assert result["largeness_score"] > 0.5


def test_natural_proofs_detector_catches_constructivity(detector, parser, sample_lean_natural_proof, tmp_path):
    """Test natural proof detector identifies constructivity."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_natural_proof)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.check_natural_proofs(proof_data, "monotone")
    
    # Should detect constructivity (counting, cardinality)
    assert result["constructivity_score"] > 0.3


def test_natural_proofs_detector_identifies_natural_proof(detector, parser, sample_lean_natural_proof, tmp_path):
    """Test natural proof detector identifies natural proofs."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_natural_proof)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.check_natural_proofs(proof_data, "monotone")
    
    # Should detect both largeness and constructivity
    assert result["is_natural_proof"] is True


def test_oracle_diagnostics_basic(detector, parser, sample_lean_monotone_parity, tmp_path):
    """Test oracle diagnostics on basic proof."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.oracle_diagnostics(proof_data)
    
    assert "core_technique" in result
    assert "oracle_dependent" in result
    assert "would_fail_with_hard_oracle" in result
    assert "interpretation" in result


def test_oracle_diagnostics_identifies_technique(detector, parser, sample_lean_monotone_parity, tmp_path):
    """Test oracle diagnostics identifies proof technique."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.oracle_diagnostics(proof_data)
    
    # Should identify induction technique
    assert result["core_technique"] == "induction"


def test_oracle_diagnostics_detects_oracle_usage(detector, parser, sample_lean_with_oracle, tmp_path):
    """Test oracle diagnostics detects oracle usage."""
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_with_oracle)
    
    proof_data = parser.parse_lean_file(lean_file)
    result = detector.oracle_diagnostics(proof_data)
    
    # Should detect oracle dependency
    assert result["oracle_dependent"] is True
    assert result["would_fail_with_hard_oracle"] is True


# === CriticAgent Tests ===

def test_critic_agent_initialization():
    """Test critic agent initializes correctly."""
    agent = CriticAgent()
    
    assert agent.name == "critic"
    assert agent.parser is not None
    assert agent.detector is not None


def test_critic_agent_plan_basic(agent_context):
    """Test critic agent planning phase."""
    agent = CriticAgent()
    
    # Add sample data to context
    agent_context.artifacts["formalizer"] = {
        "theorem_files": ["file1.lean", "file2.lean"],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "c1"}],
    }
    
    plan = agent.plan(agent_context)
    
    assert "theorem_files" in plan
    assert "conjectures" in plan
    assert "checks" in plan
    assert len(plan["theorem_files"]) == 2


def test_critic_agent_act_with_real_file(agent_context, sample_lean_monotone_parity, tmp_path):
    """Test critic agent act phase with real Lean file."""
    agent = CriticAgent()
    
    # Create temp file
    lean_file = tmp_path / "monotone_parity_n2_s12000.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    # Setup context
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [
            {
                "conjecture_id": "monotone_parity_n2_s12000",
                "circuit_type": "monotone",
            }
        ],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    assert result.status == "success"
    assert "analyses" in result.artifacts
    assert "summary" in result.artifacts
    assert len(result.artifacts["analyses"]) == 1


def test_critic_agent_generates_tags(agent_context, sample_lean_monotone_parity, tmp_path):
    """Test critic agent generates barrier tags."""
    agent = CriticAgent()
    
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "test", "circuit_type": "monotone"}],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    analysis = result.artifacts["analyses"][0]
    assert "barrier_tags" in analysis
    assert len(analysis["barrier_tags"]) > 0


def test_critic_agent_generates_assessment(agent_context, sample_lean_monotone_parity, tmp_path):
    """Test critic agent generates overall assessment."""
    agent = CriticAgent()
    
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "test", "circuit_type": "monotone"}],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    analysis = result.artifacts["analyses"][0]
    assert "overall_assessment" in analysis
    assert len(analysis["overall_assessment"]) > 0


def test_critic_agent_report_format(agent_context, sample_lean_monotone_parity, tmp_path):
    """Test critic agent generates well-formed Markdown report."""
    agent = CriticAgent()
    
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "test", "circuit_type": "monotone"}],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    report = agent.report(agent_context, result)
    
    assert "# Proof Critic Report" in report
    assert "## Executive Summary" in report
    assert "## Detailed Analysis" in report
    assert "## Recommendations" in report
    assert "## Conclusion" in report


def test_critic_agent_metrics(agent_context, sample_lean_monotone_parity, tmp_path):
    """Test critic agent generates correct metrics."""
    agent = CriticAgent()
    
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "test", "circuit_type": "monotone"}],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    assert "theorems_analyzed" in result.metrics
    assert result.metrics["theorems_analyzed"] == 1
    assert "relativizing" in result.metrics
    assert "non_relativizing" in result.metrics


def test_critic_agent_handles_multiple_files(agent_context, sample_lean_monotone_parity, sample_lean_with_oracle, tmp_path):
    """Test critic agent handles multiple theorem files."""
    agent = CriticAgent()
    
    # Create multiple files
    lean_file1 = tmp_path / "test1.lean"
    lean_file1.write_text(sample_lean_monotone_parity)
    
    lean_file2 = tmp_path / "test2.lean"
    lean_file2.write_text(sample_lean_with_oracle)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file1), str(lean_file2)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [
            {"conjecture_id": "test1", "circuit_type": "monotone"},
            {"conjecture_id": "test2", "circuit_type": "generic"},
        ],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    assert result.metrics["theorems_analyzed"] == 2
    assert len(result.artifacts["analyses"]) == 2


def test_critic_agent_summary_statistics(agent_context, sample_lean_monotone_parity, sample_lean_natural_proof, tmp_path):
    """Test critic agent generates correct summary statistics."""
    agent = CriticAgent()
    
    # Create files with different characteristics
    lean_file1 = tmp_path / "test1.lean"
    lean_file1.write_text(sample_lean_monotone_parity)
    
    lean_file2 = tmp_path / "test2.lean"
    lean_file2.write_text(sample_lean_natural_proof)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file1), str(lean_file2)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [
            {"conjecture_id": "test1", "circuit_type": "monotone"},
            {"conjecture_id": "test2", "circuit_type": "monotone"},
        ],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    summary = result.artifacts["summary"]
    assert summary["total_analyzed"] == 2
    assert summary["relativizing_count"] + summary["non_relativizing_count"] == 2


def test_critic_agent_empty_input(agent_context):
    """Test critic agent handles empty input gracefully."""
    agent = CriticAgent()
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    assert result.status == "success"
    assert result.metrics["theorems_analyzed"] == 0


# === Integration Tests ===

def test_full_agent_lifecycle(agent_context, sample_lean_monotone_parity, tmp_path):
    """Test full agent lifecycle: plan -> act -> report."""
    agent = CriticAgent()
    
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_monotone_parity)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "test", "circuit_type": "monotone"}],
    }
    
    # Plan
    plan = agent.plan(agent_context)
    assert plan is not None
    
    # Act
    result = agent.act(agent_context, plan)
    assert result.status == "success"
    
    # Report
    report = agent.report(agent_context, result)
    assert len(report) > 0
    assert "# Proof Critic Report" in report


def test_critic_detects_non_relativizing_proof(agent_context, sample_lean_with_oracle, tmp_path):
    """Test critic correctly identifies non-relativizing proof."""
    agent = CriticAgent()
    
    lean_file = tmp_path / "test.lean"
    lean_file.write_text(sample_lean_with_oracle)
    
    agent_context.artifacts["formalizer"] = {
        "theorem_files": [str(lean_file)],
    }
    agent_context.artifacts["conjecturer"] = {
        "conjectures": [{"conjecture_id": "test", "circuit_type": "generic"}],
    }
    
    plan = agent.plan(agent_context)
    result = agent.act(agent_context, plan)
    
    analysis = result.artifacts["analyses"][0]
    # Oracle usage should be detected as non-relativizing signal
    assert "oracle" in str(analysis["relativization"]["evidence"]).lower()
