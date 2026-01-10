"""
Unit tests for benchmark configuration module.

Tests configuration loading, validation, and test matrix generation.
"""

import pytest
from pathlib import Path
from pydantic import ValidationError

from search.benchmarks.config import (
    BenchmarkConfig,
    BenchmarkConfigModel,
    TestMatrix,
    Timeouts,
    OutputConfig,
)


class TestTestMatrix:
    """Tests for TestMatrix configuration."""
    
    def test_valid_matrix(self):
        """Test creating valid test matrix."""
        matrix = TestMatrix(
            name="Test Matrix",
            bet="A",
            circuit_types=["monotone", "ac0"],
            target_functions=["parity"],
            input_sizes=[2, 3],
            seed_start=100,
            seed_count=2,
        )
        
        assert matrix.name == "Test Matrix"
        assert matrix.bet == "A"
        assert matrix.circuit_types == ["monotone", "ac0"]
        assert matrix.target_functions == ["parity"]
        assert matrix.input_sizes == [2, 3]
        assert matrix.seed_start == 100
        assert matrix.seed_count == 2
    
    def test_bet_validation(self):
        """Test bet validation accepts only A/B/C/D."""
        # Valid bets
        for bet in ["A", "B", "C", "D", "a", "b", "c", "d"]:
            matrix = TestMatrix(
                name="Test",
                bet=bet,
                circuit_types=["monotone"],
                target_functions=["parity"],
                input_sizes=[2],
            )
            assert matrix.bet in ["A", "B", "C", "D"]
        
        # Invalid bet
        with pytest.raises(ValidationError):
            TestMatrix(
                name="Test",
                bet="X",
                circuit_types=["monotone"],
                target_functions=["parity"],
                input_sizes=[2],
            )
    
    def test_circuit_type_validation(self):
        """Test circuit type validation."""
        # Valid types
        matrix = TestMatrix(
            name="Test",
            bet="A",
            circuit_types=["monotone", "ac0", "formula"],
            target_functions=["parity"],
            input_sizes=[2],
        )
        assert len(matrix.circuit_types) == 3
        
        # Invalid type
        with pytest.raises(ValidationError):
            TestMatrix(
                name="Test",
                bet="A",
                circuit_types=["invalid"],
                target_functions=["parity"],
                input_sizes=[2],
            )
    
    def test_seed_count_validation(self):
        """Test seed count must be positive."""
        # Valid
        matrix = TestMatrix(
            name="Test",
            bet="A",
            circuit_types=["monotone"],
            target_functions=["parity"],
            input_sizes=[2],
            seed_count=5,
        )
        assert matrix.seed_count == 5
        
        # Invalid (zero)
        with pytest.raises(ValidationError):
            TestMatrix(
                name="Test",
                bet="A",
                circuit_types=["monotone"],
                target_functions=["parity"],
                input_sizes=[2],
                seed_count=0,
            )


class TestBenchmarkConfig:
    """Tests for BenchmarkConfig."""
    
    def test_default_config(self):
        """Test creating default configuration."""
        config = BenchmarkConfig.default()
        
        assert config.config.name == "SATurday MVP Benchmark Suite"
        assert len(config.config.test_matrices) > 0
        assert config.config_path is None
    
    def test_generate_test_instances(self):
        """Test test instance generation from matrices."""
        config = BenchmarkConfig.default()
        instances = config.generate_test_instances()
        
        # Should have generated instances
        assert len(instances) > 0
        
        # Each instance should have required fields
        for instance in instances:
            assert 'matrix_name' in instance
            assert 'bet' in instance
            assert 'circuit_type' in instance
            assert 'target_function' in instance
            assert 'n' in instance
            assert 'seed' in instance
    
    def test_generate_instances_count(self):
        """Test instance count matches matrix parameters."""
        # Create config with known parameters
        config_model = BenchmarkConfigModel(
            name="Test",
            description="Test",
            test_matrices=[
                TestMatrix(
                    name="Matrix1",
                    bet="A",
                    circuit_types=["monotone", "ac0"],  # 2 types
                    target_functions=["parity"],  # 1 function
                    input_sizes=[2, 3],  # 2 sizes
                    seed_start=100,
                    seed_count=3,  # 3 seeds
                )
            ],
        )
        config = BenchmarkConfig(config=config_model)
        
        instances = config.generate_test_instances()
        
        # Expected: 2 types × 1 function × 2 sizes × 3 seeds = 12 instances
        assert len(instances) == 12
        
        # Check seed values
        seeds = {inst['seed'] for inst in instances}
        assert seeds == {100, 101, 102}
    
    def test_get_timeout(self):
        """Test getting agent timeouts."""
        config = BenchmarkConfig.default()
        
        # Should return timeout for each agent
        assert config.get_timeout('planner') > 0
        assert config.get_timeout('conjecturer') > 0
        assert config.get_timeout('miner') > 0
        assert config.get_timeout('formalizer') > 0
        assert config.get_timeout('critic') > 0
        
        # Unknown agent should return default
        assert config.get_timeout('unknown') == 60
    
    def test_from_yaml(self, tmp_path):
        """Test loading config from YAML file."""
        # Create test YAML
        yaml_content = """
benchmark:
  name: "Test Benchmark"
  description: "Test description"
  test_matrices:
    - name: "Matrix1"
      bet: "A"
      circuit_types: ["monotone"]
      target_functions: ["parity"]
      input_sizes: [2, 3]
      seed_start: 100
      seed_count: 2
  timeouts:
    planner: 5
    conjecturer: 15
    miner: 30
    formalizer: 60
    critic: 15
  output:
    csv_path: "output/csv"
    md_path: "output/md"
    include_artifacts: true
"""
        config_file = tmp_path / "test_config.yaml"
        config_file.write_text(yaml_content)
        
        # Load config
        config = BenchmarkConfig.from_yaml(config_file)
        
        assert config.config.name == "Test Benchmark"
        assert config.config.description == "Test description"
        assert len(config.config.test_matrices) == 1
        assert config.config.timeouts.planner == 5
        assert config.config.output.csv_path == "output/csv"
        assert config.config_path == config_file
    
    def test_from_yaml_file_not_found(self):
        """Test loading from non-existent file raises error."""
        with pytest.raises(FileNotFoundError):
            BenchmarkConfig.from_yaml(Path("/nonexistent/config.yaml"))
    
    def test_from_yaml_invalid_schema(self, tmp_path):
        """Test loading invalid YAML raises validation error."""
        yaml_content = """
benchmark:
  name: "Test"
  description: "Test"
  test_matrices:
    - name: "Matrix1"
      bet: "INVALID"  # Invalid bet
      circuit_types: ["monotone"]
      target_functions: ["parity"]
      input_sizes: [2]
"""
        config_file = tmp_path / "invalid_config.yaml"
        config_file.write_text(yaml_content)
        
        with pytest.raises(ValidationError):
            BenchmarkConfig.from_yaml(config_file)
