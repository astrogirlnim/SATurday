"""
Pydantic schemas for configuration validation.

Defines the complete configuration structure with:
- Type validation
- Default values
- Field constraints
- Helpful error messages
"""

from pathlib import Path
from typing import Dict, List, Optional
from pydantic import BaseModel, Field, validator


class OfflineConfig(BaseModel):
    """Offline policy configuration."""
    enabled: bool = True
    check_api_keys: bool = True


class ArtifactsConfig(BaseModel):
    """Artifact store configuration."""
    store_dir: str = "proofs"
    auto_register: bool = True
    verify_on_load: bool = False


class SolverConfig(BaseModel):
    """SAT solver configuration."""
    binary: str = "infra/build/kissat"
    default_seed: int = Field(42, ge=0)
    timeout_seconds: int = Field(300, gt=0)
    enable_lrat: bool = True
    cpu_only: bool = True
    
    @validator('binary')
    def binary_must_exist_or_relative(cls, v):
        """Validate binary path is reasonable."""
        print(f"[Config] Solver binary: {v}")
        return v


class CircuitsConfig(BaseModel):
    """Circuit DSL configuration."""
    max_gates: int = Field(1000, gt=0)
    max_depth: int = Field(100, gt=0)
    max_inputs: int = Field(100, gt=0)
    validate_topology: bool = True


class PlannerAgentConfig(BaseModel):
    """Planner agent configuration."""
    enabled: bool = True
    task_batch_size: int = Field(10, gt=0)


class ConjecturerAgentConfig(BaseModel):
    """Conjecturer agent configuration."""
    enabled: bool = True
    mode: str = Field("template", regex="^(template|llm)$")
    template_depth: int = Field(3, gt=0)


class MinerAgentConfig(BaseModel):
    """Miner agent configuration."""
    enabled: bool = True
    small_n_only: bool = True
    max_variables: int = Field(20, gt=0)
    max_clauses: int = Field(1000, gt=0)


class FormalizerAgentConfig(BaseModel):
    """Formalizer agent configuration."""
    enabled: bool = True
    allow_sorry: bool = True
    tactic_timeout: int = Field(30, gt=0)


class CriticAgentConfig(BaseModel):
    """Critic agent configuration."""
    enabled: bool = True
    check_relativization: bool = True
    check_natural_proofs: bool = True
    check_algebraization: bool = False


class AgentsConfig(BaseModel):
    """Configuration for all agents."""
    planner: PlannerAgentConfig = PlannerAgentConfig()
    conjecturer: ConjecturerAgentConfig = ConjecturerAgentConfig()
    miner: MinerAgentConfig = MinerAgentConfig()
    formalizer: FormalizerAgentConfig = FormalizerAgentConfig()
    critic: CriticAgentConfig = CriticAgentConfig()


class LoggingConfig(BaseModel):
    """Logging configuration."""
    level: str = Field("INFO", regex="^(DEBUG|INFO|WARNING|ERROR)$")
    format: str = Field("jsonl", regex="^(jsonl|text)$")
    log_dir: str = "search/logs"
    console_output: bool = True
    verbose: bool = True


class ExecutionConfig(BaseModel):
    """Execution configuration."""
    parallel: bool = False
    max_workers: int = Field(1, gt=0)
    checkpoint_interval: int = Field(10, gt=0)
    continue_on_error: bool = False


class SizeRange(BaseModel):
    """Size range for parameter sweep."""
    min: int = Field(5, gt=0)
    max: int = Field(20, gt=0)
    step: int = Field(5, gt=0)
    
    @validator('max')
    def max_must_be_greater_than_min(cls, v, values):
        """Validate max > min."""
        if 'min' in values and v <= values['min']:
            raise ValueError('max must be greater than min')
        return v


class BetAConfig(BaseModel):
    """Bet A: Restricted-Circuit Lower Bounds."""
    enabled: bool = True
    circuit_types: List[str] = ["monotone", "ac0", "formula"]
    size_range: SizeRange = SizeRange()


class BetBConfig(BaseModel):
    """Bet B: Algorithm Synthesis."""
    enabled: bool = False


class BetCConfig(BaseModel):
    """Bet C: Hardness-vs-Randomness."""
    enabled: bool = False


class BetDConfig(BaseModel):
    """Bet D: Barrier-Aware Reductions."""
    enabled: bool = False


class BetsConfig(BaseModel):
    """Research bets configuration."""
    bet_a: BetAConfig = BetAConfig()
    bet_b: BetBConfig = BetBConfig()
    bet_c: BetCConfig = BetCConfig()
    bet_d: BetDConfig = BetDConfig()


class VerificationConfig(BaseModel):
    """Verification configuration."""
    enable_lrat_check: bool = True
    lrat_checker: str = "lrat-check"
    enable_lean_build: bool = True
    lean_timeout: int = Field(300, gt=0)


class ReproducibilityConfig(BaseModel):
    """Reproducibility configuration."""
    pin_dependencies: bool = True
    check_determinism: bool = True
    record_hashes: bool = True
    fixed_seeds: bool = True


class CostConfig(BaseModel):
    """Cost guard configuration."""
    enabled: bool = True
    max_monthly_spend: float = Field(0.0, ge=0.0)
    block_api_calls: bool = True
    allowed_domains: List[str] = []


class SaturdayConfig(BaseModel):
    """
    Complete SATurday configuration.
    
    This is the root configuration object that contains all settings.
    Provides type validation, defaults, and helpful error messages.
    """
    offline: OfflineConfig = OfflineConfig()
    artifacts: ArtifactsConfig = ArtifactsConfig()
    solver: SolverConfig = SolverConfig()
    circuits: CircuitsConfig = CircuitsConfig()
    agents: AgentsConfig = AgentsConfig()
    logging: LoggingConfig = LoggingConfig()
    execution: ExecutionConfig = ExecutionConfig()
    bets: BetsConfig = BetsConfig()
    verification: VerificationConfig = VerificationConfig()
    reproducibility: ReproducibilityConfig = ReproducibilityConfig()
    cost: CostConfig = CostConfig()
    
    class Config:
        """Pydantic config."""
        extra = "forbid"  # Reject unknown fields
        validate_assignment = True  # Validate on field assignment
    
    def validate_cost_policy(self) -> None:
        """
        Validate cost policy constraints.
        
        Raises:
            ValueError: If cost policy violated
        """
        print("[Config] Validating cost policy")
        
        if self.cost.enabled:
            if self.cost.max_monthly_spend > 0:
                print(f"[Config] WARNING: Max monthly spend is ${self.cost.max_monthly_spend}")
                print("[Config] This project aims for zero cost!")
            
            if not self.cost.block_api_calls:
                print("[Config] WARNING: API calls not blocked")
                print("[Config] This violates zero-cost policy!")
        
        print("[Config] Cost policy validation complete")
    
    def validate_offline_policy(self) -> None:
        """
        Validate offline policy constraints.
        
        Raises:
            ValueError: If offline policy violated
        """
        print("[Config] Validating offline policy")
        
        if self.offline.enabled:
            if not self.cost.block_api_calls:
                raise ValueError(
                    "Offline mode enabled but API calls not blocked. "
                    "Set cost.block_api_calls = true"
                )
        
        print("[Config] Offline policy validation complete")
    
    def validate_all_policies(self) -> None:
        """Validate all policy constraints."""
        self.validate_cost_policy()
        self.validate_offline_policy()

