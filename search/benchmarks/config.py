"""
Benchmark configuration schemas and loaders.

Defines Pydantic models for benchmark configuration and provides
utilities for loading from YAML files.
"""

from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

import yaml
from pydantic import BaseModel, Field, field_validator


class TestMatrix(BaseModel):
    """Configuration for a single test matrix.
    
    Attributes:
        name: Human-readable matrix name
        bet: Research bet identifier (A/B/C/D)
        circuit_types: List of circuit types to test
        target_functions: List of target functions (parity, majority, etc.)
        input_sizes: List of input sizes (n values)
        seed_start: Starting seed value
        seed_count: Number of seeds per configuration
    """
    name: str
    bet: str
    circuit_types: List[str]
    target_functions: List[str]
    input_sizes: List[int]
    seed_start: int = Field(default=12000)
    seed_count: int = Field(default=3, gt=0)
    
    @field_validator('bet')
    @classmethod
    def validate_bet(cls, v: str) -> str:
        """Validate bet is one of A/B/C/D."""
        if v.upper() not in ['A', 'B', 'C', 'D']:
            raise ValueError(f"Bet must be one of A/B/C/D, got {v}")
        return v.upper()
    
    @field_validator('circuit_types')
    @classmethod
    def validate_circuit_types(cls, v: List[str]) -> List[str]:
        """Validate circuit types."""
        valid = {'monotone', 'ac0', 'formula'}
        for ct in v:
            if ct not in valid:
                raise ValueError(f"Invalid circuit type: {ct}. Must be one of {valid}")
        return v


class Timeouts(BaseModel):
    """Per-agent timeout configuration.
    
    Attributes:
        planner: Planner agent timeout in seconds
        conjecturer: Conjecturer agent timeout in seconds
        miner: Miner agent timeout in seconds
        formalizer: Formalizer agent timeout in seconds
        critic: Critic agent timeout in seconds
    """
    planner: int = Field(default=10, gt=0)
    conjecturer: int = Field(default=30, gt=0)
    miner: int = Field(default=60, gt=0)
    formalizer: int = Field(default=120, gt=0)
    critic: int = Field(default=30, gt=0)


class OutputConfig(BaseModel):
    """Output configuration for benchmark results.
    
    Attributes:
        csv_path: Directory for CSV output
        md_path: Directory for Markdown output
        include_artifacts: Whether to include artifact hashes in output
    """
    csv_path: str = Field(default="docs/benchmarks")
    md_path: str = Field(default="docs/benchmarks")
    include_artifacts: bool = Field(default=True)


class BenchmarkConfigModel(BaseModel):
    """Top-level benchmark configuration.
    
    Attributes:
        name: Benchmark suite name
        description: Human-readable description
        test_matrices: List of test matrix configurations
        timeouts: Per-agent timeout configuration
        output: Output configuration
    """
    name: str
    description: str
    test_matrices: List[TestMatrix]
    timeouts: Timeouts = Field(default_factory=Timeouts)
    output: OutputConfig = Field(default_factory=OutputConfig)


@dataclass
class BenchmarkConfig:
    """Benchmark configuration with convenience methods.
    
    Attributes:
        config: Pydantic configuration model
        config_path: Path to configuration file (if loaded from file)
    """
    config: BenchmarkConfigModel
    config_path: Optional[Path] = None
    
    @classmethod
    def from_yaml(cls, path: Path) -> "BenchmarkConfig":
        """Load benchmark configuration from YAML file.
        
        Args:
            path: Path to YAML configuration file
            
        Returns:
            BenchmarkConfig: Loaded configuration
            
        Raises:
            FileNotFoundError: If config file doesn't exist
            yaml.YAMLError: If config file is invalid YAML
            pydantic.ValidationError: If config doesn't match schema
        """
        if not path.exists():
            raise FileNotFoundError(f"Config file not found: {path}")
        
        with open(path, 'r') as f:
            data = yaml.safe_load(f)
        
        # Validate with Pydantic
        config_model = BenchmarkConfigModel(**data['benchmark'])
        
        return cls(config=config_model, config_path=path)
    
    @classmethod
    def default(cls) -> "BenchmarkConfig":
        """Create default benchmark configuration.
        
        Returns:
            BenchmarkConfig: Configuration with sensible defaults
        """
        config = BenchmarkConfigModel(
            name="SATurday MVP Benchmark Suite",
            description="Deterministic validation of agent pipeline",
            test_matrices=[
                TestMatrix(
                    name="BetA_CircuitBounds_Tiny",
                    bet="A",
                    circuit_types=["monotone", "ac0", "formula"],
                    target_functions=["parity", "majority"],
                    input_sizes=[2, 3, 4, 5],
                    seed_start=12000,
                    seed_count=3,
                )
            ],
            timeouts=Timeouts(),
            output=OutputConfig(),
        )
        return cls(config=config)
    
    def generate_test_instances(self) -> List[Dict]:
        """Generate all test instances from configuration matrices.
        
        Returns:
            List[Dict]: List of test instance configurations
        """
        instances = []
        
        for matrix in self.config.test_matrices:
            for circuit_type in matrix.circuit_types:
                for target_fn in matrix.target_functions:
                    for n in matrix.input_sizes:
                        for seed_offset in range(matrix.seed_count):
                            seed = matrix.seed_start + seed_offset
                            
                            instance = {
                                'matrix_name': matrix.name,
                                'bet': matrix.bet,
                                'circuit_type': circuit_type,
                                'target_function': target_fn,
                                'n': n,
                                'seed': seed,
                            }
                            instances.append(instance)
        
        return instances
    
    def get_timeout(self, agent: str) -> int:
        """Get timeout for specific agent.
        
        Args:
            agent: Agent name (planner, conjecturer, miner, formalizer, critic)
            
        Returns:
            int: Timeout in seconds
        """
        return getattr(self.config.timeouts, agent, 60)
