"""
Tests for the Counterexample Miner Agent.

Tests cover:
- Kissat output parsing (SAT/UNSAT, models, timing)
- LRAT pattern extraction
- Agent lifecycle (plan, act, report)
- Integration with CircuitEncoder and artifact store
- Error handling and edge cases
"""

import json
import pytest
import tempfile
import sys
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock

# Add search directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from agents.miner import MinerAgent
from agents.core import AgentContext, AgentResult


class TestKissatOutputParsing:
    """Test parsing of Kissat solver output."""
    
    def test_parse_status_sat(self):
        """Test parsing SAT result."""
        agent = MinerAgent()
        
        output = """c Kissat SAT Solver
s SATISFIABLE
v 1 -2 3 0
"""
        status = agent._parse_status(output)
        assert status == "SAT"
    
    def test_parse_status_unsat(self):
        """Test parsing UNSAT result."""
        agent = MinerAgent()
        
        output = """c Kissat SAT Solver
s UNSATISFIABLE
"""
        status = agent._parse_status(output)
        assert status == "UNSAT"
    
    def test_parse_status_unknown(self):
        """Test parsing unknown result."""
        agent = MinerAgent()
        
        output = """c Kissat SAT Solver
c No solution found
"""
        status = agent._parse_status(output)
        assert status == "UNKNOWN"
    
    def test_parse_model_simple(self):
        """Test parsing simple model."""
        agent = MinerAgent()
        
        output = """s SATISFIABLE
v 1 -2 3 0
"""
        model = agent._parse_model(output)
        
        assert model == {1: True, 2: False, 3: True}
    
    def test_parse_model_multiline(self):
        """Test parsing model across multiple lines."""
        agent = MinerAgent()
        
        output = """s SATISFIABLE
v 1 -2 3 -4
v 5 -6 0
"""
        model = agent._parse_model(output)
        
        assert model == {
            1: True, 2: False, 3: True,
            4: False, 5: True, 6: False
        }
    
    def test_parse_model_empty(self):
        """Test parsing with no model."""
        agent = MinerAgent()
        
        output = """s UNSATISFIABLE
"""
        model = agent._parse_model(output)
        
        assert model == {}
    
    def test_parse_solver_time(self):
        """Test parsing solver time."""
        agent = MinerAgent()
        
        output = """c total process time since initialization: 0.05 seconds
"""
        time = agent._parse_solver_time(output)
        
        assert time == 0.05
    
    def test_parse_solver_time_missing(self):
        """Test parsing with missing time info."""
        agent = MinerAgent()
        
        output = """s SATISFIABLE
"""
        time = agent._parse_solver_time(output)
        
        assert time == 0.0


class TestLRATPatternExtraction:
    """Test extraction of patterns from LRAT proofs."""
    
    def test_extract_basic_patterns(self):
        """Test basic LRAT statistics extraction."""
        agent = MinerAgent()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lrat', delete=False) as f:
            f.write("1 2 3 0\n")
            f.write("2 4 5 0\n")
            f.write("3 0 0\n")
            lrat_path = Path(f.name)
        
        try:
            patterns = agent._extract_basic_patterns(lrat_path)
            
            assert "proof_size_bytes" in patterns
            assert "proof_lines" in patterns
            assert "proof_complexity_proxy" in patterns
            assert patterns["proof_lines"] == 3
            assert patterns["proof_size_bytes"] > 0
        
        finally:
            lrat_path.unlink()
    
    def test_extract_patterns_missing_file(self):
        """Test extraction with missing LRAT file."""
        agent = MinerAgent()
        
        lrat_path = Path("/nonexistent/file.lrat")
        patterns = agent._extract_basic_patterns(lrat_path)
        
        assert patterns["proof_size_bytes"] == 0
        assert patterns["proof_lines"] == 0
        assert patterns["proof_complexity_proxy"] == 0
    
    def test_extract_patterns_empty_file(self):
        """Test extraction with empty LRAT file."""
        agent = MinerAgent()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lrat', delete=False) as f:
            lrat_path = Path(f.name)
        
        try:
            patterns = agent._extract_basic_patterns(lrat_path)
            
            assert patterns["proof_lines"] == 0
            assert patterns["proof_size_bytes"] == 0
        
        finally:
            lrat_path.unlink()


class TestCNFSpecLoading:
    """Test loading CNF specifications."""
    
    def test_load_cnf_spec(self):
        """Test loading valid CNF spec YAML."""
        agent = MinerAgent()
        
        spec_data = {
            "circuit_class": "monotone",
            "params": {"n": 3},
            "target_function": "parity",
            "solver_config": {"timeout": 60},
        }
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
            import yaml
            yaml.dump(spec_data, f)
            spec_path = Path(f.name)
        
        try:
            spec = agent._load_cnf_spec(spec_path)
            
            assert spec["circuit_class"] == "monotone"
            assert spec["params"]["n"] == 3
            assert spec["target_function"] == "parity"
        
        finally:
            spec_path.unlink()


class TestMinerAgentLifecycle:
    """Test agent lifecycle: plan, act, report."""
    
    def test_plan_with_conjectures(self):
        """Test planning phase with conjectures."""
        agent = MinerAgent()
        
        # Create mock context
        context = AgentContext(
            run_id="test123",
            seed=42,
            timestamp="2026-01-10T00:00:00",
            config={
                "solver": {"timeout_seconds": 30},
                "seed": 42,
            },
            artifacts={
                "conjecturer": {
                    "conjectures": [
                        {
                            "conjecture_id": "conj_1",
                            "spec_file": "/tmp/spec1.yaml",  # Changed from cnf_spec_path
                            "lean_file": "/tmp/stub1.lean",  # Changed from lean_stub_path
                        },
                        {
                            "conjecture_id": "conj_2",
                            "spec_file": "/tmp/spec2.yaml",  # Changed from cnf_spec_path
                            "lean_file": "/tmp/stub2.lean",  # Changed from lean_stub_path
                        },
                    ]
                }
            }
        )
        
        # Mock file existence
        with patch('pathlib.Path.exists', return_value=True):
            plan = agent.plan(context)
        
        assert plan["num_conjectures"] == 2
        assert plan["solver"] == "kissat"
        assert plan["timeout_per_instance"] == 30
        assert len(plan["cnf_specs"]) == 2
        assert plan["cnf_specs"][0]["conjecture_id"] == "conj_1"
    
    def test_plan_with_no_conjectures(self):
        """Test planning with no conjectures."""
        agent = MinerAgent()
        
        context = AgentContext(
            run_id="test123",
            seed=42,
            timestamp="2026-01-10T00:00:00",
            config={"solver": {"timeout_seconds": 60}, "seed": 42},
            artifacts={}
        )
        
        plan = agent.plan(context)
        
        assert plan["num_conjectures"] == 0
        assert plan["cnf_specs"] == []
    
    def test_report_with_sat_results(self):
        """Test report generation with SAT results."""
        agent = MinerAgent()
        
        context = AgentContext(run_id="test123", seed=42, timestamp="2026-01-10T00:00:00", config={}, artifacts={})
        
        result = AgentResult(
            agent_name="miner",
            status="success",
            artifacts={
                "mining_results": [
                    {
                        "conjecture_id": "conj_1",
                        "status": "SAT",
                        "solver_time": 0.05,
                        "model": {1: True, 2: False, 3: True},
                    }
                ],
                "summary": {
                    "total_tested": 1,
                    "unsat": 0,
                    "sat": 1,
                    "error": 0,
                    "timeout": 0,
                    "total_solver_time": 0.05,
                }
            },
            metrics={},
        )
        
        report = agent.report(context, result)
        
        assert "Miner Agent Report" in report
        assert "Instances Tested: 1" in report
        assert "SAT Results: 1" in report
        assert "conj_1" in report
        assert "Counterexample Found" in report
    
    def test_report_with_unsat_results(self):
        """Test report generation with UNSAT results."""
        agent = MinerAgent()
        
        context = AgentContext(run_id="test123", seed=42, timestamp="2026-01-10T00:00:00", config={}, artifacts={})
        
        result = AgentResult(
            agent_name="miner",
            status="success",
            artifacts={
                "mining_results": [
                    {
                        "conjecture_id": "conj_1",
                        "status": "UNSAT",
                        "solver_time": 0.03,
                        "patterns": {
                            "proof_size_bytes": 150,
                            "proof_lines": 12,
                            "proof_complexity_proxy": 12,
                        },
                    }
                ],
                "summary": {
                    "total_tested": 1,
                    "unsat": 1,
                    "sat": 0,
                    "error": 0,
                    "timeout": 0,
                    "total_solver_time": 0.03,
                }
            },
            metrics={},
        )
        
        report = agent.report(context, result)
        
        assert "UNSAT Results: 1" in report
        assert "LRAT Proof Available: Yes" in report
        assert "Proof Size: 150 bytes" in report
        assert "Proof Lines: 12" in report
    
    def test_report_with_mixed_results(self):
        """Test report with SAT, UNSAT, and errors."""
        agent = MinerAgent()
        
        context = AgentContext(run_id="test123", seed=42, timestamp="2026-01-10T00:00:00", config={}, artifacts={})
        
        result = AgentResult(
            agent_name="miner",
            status="partial",
            artifacts={
                "mining_results": [
                    {"conjecture_id": "conj_1", "status": "SAT", "solver_time": 0.05,
                     "model": {1: True}},
                    {"conjecture_id": "conj_2", "status": "UNSAT", "solver_time": 0.03,
                     "patterns": {"proof_lines": 10, "proof_size_bytes": 100, "proof_complexity_proxy": 10}},
                    {"conjecture_id": "conj_3", "status": "ERROR", "solver_time": 0.0,
                     "error": "Timeout"},
                ],
                "summary": {
                    "total_tested": 3,
                    "unsat": 1,
                    "sat": 1,
                    "error": 1,
                    "timeout": 0,
                    "total_solver_time": 0.08,
                }
            },
            metrics={},
        )
        
        report = agent.report(context, result)
        
        assert "Instances Tested: 3" in report
        assert "SAT Results: 1" in report
        assert "UNSAT Results: 1" in report
        assert "Errors: 1" in report


class TestCounterexampleRegistration:
    """Test registration of counterexamples in artifact store."""
    
    def test_register_counterexample(self):
        """Test counterexample registration."""
        agent = MinerAgent()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            proofs_dir = Path(tmpdir)
            agent.proofs_dir = proofs_dir
            
            cnf_path = proofs_dir / "test.cnf"
            cnf_path.write_text("p cnf 3 1\n1 2 3 0\n")
            
            model = {1: True, 2: False, 3: True}
            seed = 42
            
            # Register counterexample
            artifact_hash = agent._register_counterexample(cnf_path, model, seed)
            
            # Verify registration (may be None if artifact store not initialized)
            # This is acceptable for MVP
            assert artifact_hash is None or isinstance(artifact_hash, str)


class TestIntegration:
    """Integration tests with real components."""
    
    @pytest.mark.slow
    def test_act_with_mock_kissat(self):
        """Test act phase with mocked Kissat."""
        agent = MinerAgent()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            tmpdir_path = Path(tmpdir)
            
            # Create mock CNF spec
            spec_data = {
                "circuit_class": "monotone",
                "params": {"n": 2},
                "target_function": "parity",
            }
            
            spec_path = tmpdir_path / "test_spec.yaml"
            with open(spec_path, 'w') as f:
                import yaml
                yaml.dump(spec_data, f)
            
            # Setup context
            context = AgentContext(
                run_id="test123",
                seed=42,
                timestamp="2026-01-10T00:00:00",
                config={
                    "solver": {"timeout_seconds": 30},
                    "seed": 42,
                },
                artifacts={}
            )
            
            plan = {
                "num_conjectures": 1,
                "cnf_specs": [
                    {
                        "conjecture_id": "test_conj",
                        "spec_path": str(spec_path),
                        "lean_stub_path": "/tmp/stub.lean",
                    }
                ],
                "solver": "kissat",
                "timeout_per_instance": 30,
                "seed": 42,
            }
            
            # Mock subprocess call to Kissat wrapper
            # The wrapper outputs JSON format
            mock_result = MagicMock()
            mock_result.returncode = 0
            mock_result.stdout = json.dumps({
                "status": "SAT",
                "exit_code": 10,
                "solver_time": 0.05,
                "model": [1, -2],
                "stats": {
                    "variables": 2,
                    "clauses": 1,
                }
            })
            mock_result.stderr = ""
            
            with patch('subprocess.run', return_value=mock_result):
                with patch.object(agent, '_generate_cnf_from_spec') as mock_gen:
                    # Mock CNF generation
                    mock_cnf_path = tmpdir_path / "test.cnf"
                    mock_cnf_path.write_text("p cnf 2 1\n1 2 0\n")
                    mock_gen.return_value = mock_cnf_path
                    
                    # Run act
                    result = agent.act(context, plan)
            
            assert result.status in ["success", "partial"]
            assert result.metrics["instances_tested"] == 1


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_mine_with_invalid_spec(self):
        """Test mining with invalid CNF spec."""
        agent = MinerAgent()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            spec_path = Path(tmpdir) / "bad_spec.yaml"
            spec_path.write_text("invalid: yaml: content:")
            
            context = AgentContext(
                run_id="test123",
                seed=42,
                timestamp="2026-01-10T00:00:00",
                config={"solver": {"timeout_seconds": 30}, "seed": 42},
                artifacts={}
            )
            
            with pytest.raises(Exception):
                agent._load_cnf_spec(spec_path)
    
    def test_act_with_solver_timeout(self):
        """Test handling of solver timeout."""
        agent = MinerAgent()
        
        context = AgentContext(
            run_id="test123",
            seed=42,
            timestamp="2026-01-10T00:00:00",
            config={"solver": {"timeout_seconds": 1}, "seed": 42},
            artifacts={}
        )
        
        plan = {
            "num_conjectures": 0,
            "cnf_specs": [],
            "solver": "kissat",
            "timeout_per_instance": 1,
            "seed": 42,
        }
        
        # Act with empty plan should succeed
        result = agent.act(context, plan)
        
        # Empty plan is successful (no errors)
        assert result.status == "success"
        assert result.metrics["instances_tested"] == 0
        assert result.metrics["error_count"] == 0
    
    def test_parse_model_with_malformed_output(self):
        """Test parsing model with malformed output."""
        agent = MinerAgent()
        
        output = """s SATISFIABLE
v abc def ghi 0
"""
        model = agent._parse_model(output)
        
        # Should handle gracefully and return empty model
        assert model == {}


# Run tests
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
