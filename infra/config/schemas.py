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


class LLMConfig(BaseModel):
    """LLM configuration for the legacy conjecturer agent.

    Defaults align with the local saturday_loop formalize role. Prefer
    Goedel-Prover-V2-8B via an OpenAI compatible server when available;
    qwen2.5-coder:14b is the Ollama packaged default.
    """
    enabled: bool = False
    model: str = "qwen2.5-coder:14b"
    endpoint: str = "http://localhost:11434"
    num_predict: int = 8192
    temperature: float = 0.1


class SaturdayRoleLLMConfig(BaseModel):
    """Per role local model settings for the saturday CLI loop."""
    model: str
    num_predict: int = Field(8192, gt=0)
    temperature: float = Field(0.1, ge=0.0)


class SaturdayRemoteConfig(BaseModel):
    """
    Optional hosted LLM escalation (OpenRouter).

    Off by default. Enable with satday --remote (or remote.enabled=true) and
    set OPENROUTER_API_KEY in the environment. Never commit the key.
    """
    enabled: bool = False
    # escalate: local formalize first, then remote if apply fails
    # remote: formalize uses OpenRouter only
    mode: str = Field("escalate", pattern="^(escalate|remote)$")
    endpoint: str = "https://openrouter.ai/api/v1"
    api_style: str = Field("openai_compatible", pattern="^(openai_compatible)$")
    api_key_env: str = "OPENROUTER_API_KEY"
    timeout_seconds: int = Field(600, gt=0)
    use_for_formalize: bool = True
    use_for_prove: bool = False
    use_for_audit: bool = False
    formalize_model: str = "anthropic/claude-sonnet-4"
    prove_model: str = "anthropic/claude-sonnet-4"
    audit_model: str = "anthropic/claude-sonnet-4"
    # Optional OpenRouter ranking headers (no secrets)
    http_referer: str = "https://github.com/astrogirlnim/SATurday"
    app_title: str = "SATurday"


class SaturdayLoopConfig(BaseModel):
    """
    Local saturday research loop (option A: CLI + localhost models).

    This is the offline replacement for Cursor cloud agents driving the
    saturday skill. Falsify never calls an LLM. Optional remote escalation
    is gated by saturday_loop.remote and CLI --remote.
    """
    enabled: bool = True
    endpoint: str = "http://localhost:11434"
    # ollama = /api/generate; openai_compatible = /v1/chat/completions
    api_style: str = Field("ollama", pattern="^(ollama|openai_compatible)$")
    timeout_seconds: int = Field(600, gt=0)
    require_local: bool = True
    # Role models sized for Apple Silicon 16GB+ unified memory
    prove: SaturdayRoleLLMConfig = SaturdayRoleLLMConfig(
        model="qwen2.5:14b",
        num_predict=8192,
        temperature=0.2,
    )
    formalize: SaturdayRoleLLMConfig = SaturdayRoleLLMConfig(
        model="qwen2.5-coder:14b",
        num_predict=8192,
        temperature=0.1,
    )
    audit: SaturdayRoleLLMConfig = SaturdayRoleLLMConfig(
        model="qwen2.5:14b",
        num_predict=4096,
        temperature=0.1,
    )
    remote: SaturdayRemoteConfig = SaturdayRemoteConfig()
    falsify_family: str = "php"
    falsify_n_min: int = Field(4, gt=0)
    falsify_n_max: int = Field(10, gt=0)
    falsify_seed: int = Field(42, ge=0)
    draft_dir: str = "search/logs/saturday_drafts"
    sessions_path: str = "search/logs/saturday_sessions.jsonl"
    # When true, formalize auto-applies Frontier drafts into theory/ if lake build stays green
    auto_apply: bool = True
    # Local CLI loop defaults (satday loop); 0 cycles means run until interrupted
    loop_sleep_seconds: int = Field(90, ge=0)
    loop_max_cycles: int = Field(1, ge=0)
    loop_parallel_default: bool = False


class ConjecturerAgentConfig(BaseModel):
    """Conjecturer agent configuration."""
    enabled: bool = True
    mode: str = Field("template", pattern="^(template|llm|llm\\+template)$")
    template_depth: int = Field(3, gt=0)
    max_conjectures: int = Field(1000, gt=0)
    llm: LLMConfig = LLMConfig()


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
    # V14: number of LLM attempts per sorry-containing proof before giving up
    close_sorry_attempts: int = Field(3, gt=0)
    # V14: use LLM to attempt closing sorry stubs (requires LLM enabled)
    close_sorry_with_llm: bool = True


class CriticAgentConfig(BaseModel):
    """Critic agent configuration."""
    enabled: bool = True
    check_relativization: bool = True
    check_natural_proofs: bool = True
    check_algebraization: bool = False
    # V10: Use oracle-world diagnostics (explicit witness construction) instead of heuristics
    oracle_world_diagnostics: bool = True
    # V10: If LLM active, feed oracle witness back to conjecturer for non-rel tweak proposals
    llm_feedback_loop: bool = True


class AgentsConfig(BaseModel):
    """Configuration for all agents."""
    planner: PlannerAgentConfig = PlannerAgentConfig()
    conjecturer: ConjecturerAgentConfig = ConjecturerAgentConfig()
    miner: MinerAgentConfig = MinerAgentConfig()
    formalizer: FormalizerAgentConfig = FormalizerAgentConfig()
    critic: CriticAgentConfig = CriticAgentConfig()


class LoggingConfig(BaseModel):
    """Logging configuration."""
    level: str = Field("INFO", pattern="^(DEBUG|INFO|WARNING|ERROR)$")
    format: str = Field("jsonl", pattern="^(jsonl|text)$")
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
    step: Optional[int] = None  # None means use automatic progression heuristic

    @validator('max')
    def max_must_be_gte_min(cls, v, values):
        """Validate max >= min (single-point ranges are allowed)."""
        if 'min' in values and v < values['min']:
            raise ValueError('max must be >= min')
        return v


class SeedRange(BaseModel):
    """Seed range configuration."""
    start: int = Field(12000, ge=0)
    count: int = Field(3, gt=0)


class BetAConfig(BaseModel):
    """Bet A: Restricted-Circuit Lower Bounds."""
    enabled: bool = True
    circuit_types: List[str] = ["monotone", "ac0", "formula"]
    target_functions: List[str] = ["parity", "majority", "threshold_2", "threshold_3"]
    size_range: SizeRange = SizeRange()
    seed_range: SeedRange = SeedRange()
    # V4b: threshold above which algebraic encoding is used instead of streaming.
    # n >= algebraic_threshold and function == parity => "algebraic" mode (O(k^2+n) clauses).
    # Set to 11 to apply V4b for all large-n parity instances including n=16-20.
    algebraic_threshold: int = 11


class BetBConfig(BaseModel):
    """Bet B: Algorithm Synthesis with Polynomial Bounds."""
    enabled: bool = False
    algorithm_schemas: List[str] = ["sorting", "searching", "graph_reach"]
    size_range: SizeRange = SizeRange(min=2, max=6)
    seed_range: SeedRange = SeedRange(start=20000, count=2)


class BetCConfig(BaseModel):
    """Bet C: Hardness-vs-Randomness (V7)."""
    enabled: bool = False
    # Correlation test schemas: hardness_correlation, prg_security, nw_implication
    test_schemas: List[str] = ["hardness_correlation", "prg_security", "nw_implication"]
    # Circuit types to test correlation against
    circuit_types: List[str] = ["monotone", "ac0"]
    # Target functions to probe
    target_functions: List[str] = ["parity"]
    # Size range for the correlation test (n = number of inputs)
    size_range: SizeRange = SizeRange(min=2, max=6)
    # Seed range
    seed_range: SeedRange = SeedRange(start=30000, count=2)
    # Epsilon for correlation threshold (correlation > 0.5 + epsilon)
    epsilon: float = 0.1


class BetDConfig(BaseModel):
    """Bet D: Barrier-Aware Reductions (V8)."""
    enabled: bool = False
    # Reduction schema types to probe:
    #   non_relativizing_reduction: reduction whose proof does not relativize
    #   oracle_barrier_test: explicitly tests whether reduction survives oracle worlds
    #   algebraization_reduction: uses algebraic techniques (IP, MIP) to escape barriers
    reduction_schemas: List[str] = [
        "non_relativizing_reduction",
        "oracle_barrier_test",
        "algebraization_reduction",
    ]
    # Source/target problem pairs for reductions
    source_problems: List[str] = ["sat", "3sat", "circuit_sat"]
    target_problems: List[str] = ["parity_lower_bound", "circuit_lower_bound"]
    # Size range (n = number of inputs / problem size)
    size_range: SizeRange = SizeRange(min=2, max=6)
    # Seed range
    seed_range: SeedRange = SeedRange(start=40000, count=2)


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
    saturday_loop: SaturdayLoopConfig = SaturdayLoopConfig()
    
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

