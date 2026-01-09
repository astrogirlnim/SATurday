"""
Agent Supervisor - Orchestrates multi-agent research cycles.

The supervisor:
- Loads YAML execution plans
- Creates execution context
- Sequences agents: Planner -> Conjecturer -> Miner -> Formalizer -> Critic
- Aggregates results and logs to JSONL
- Enforces offline policy and cost guards
"""

import json
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional, Union

import yaml

# Add parent to path for imports
parent_dir = Path(__file__).parent.parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from search.agents.core import AgentBase, AgentContext, AgentResult
from search.agents.planner import PlannerAgent
from search.agents.conjecturer import ConjecturerAgent
from search.agents.miner import MinerAgent
from search.agents.formalizer import FormalizerAgent
from search.agents.critic import CriticAgent
from infra.config.schemas import SaturdayConfig
from infra.config.loader import load_config


class Supervisor:
    """
    Orchestrates execution of agent pipeline.
    """
    
    def __init__(
        self,
        config: Optional[Union[SaturdayConfig, Dict[str, Any]]] = None,
        log_dir: Optional[Path] = None,
        config_file: Optional[Path] = None,
    ):
        """
        Initialize supervisor with configuration.
        
        Args:
            config: Configuration (SaturdayConfig, dict, or None to load defaults)
            log_dir: Directory for JSONL logs (overrides config if provided)
            config_file: Optional config file to load (if config is None)
        """
        # Load configuration
        if config is None:
            print("[SUPERVISOR] Loading default configuration")
            self.config = load_config(config_file=config_file)
        elif isinstance(config, dict):
            print("[SUPERVISOR] Converting dict config to SaturdayConfig")
            self.config = SaturdayConfig(**config)
        else:
            self.config = config
        
        # Validate policies
        self.config.validate_all_policies()
        
        # Get offline mode from config
        self.offline = self.config.offline.enabled
        
        # Set up logging directory
        if log_dir is None:
            # Use config value
            log_dir_str = self.config.logging.log_dir
            # Convert to absolute path if relative
            if not Path(log_dir_str).is_absolute():
                repo_root = Path(__file__).parent.parent.parent
                self.log_dir = repo_root / log_dir_str
            else:
                self.log_dir = Path(log_dir_str)
        else:
            self.log_dir = Path(log_dir)
        
        self.log_dir.mkdir(parents=True, exist_ok=True)
        
        # Initialize agents based on configuration
        self.agents: List[AgentBase] = []
        
        if self.config.agents.planner.enabled:
            self.agents.append(PlannerAgent())
        if self.config.agents.conjecturer.enabled:
            self.agents.append(ConjecturerAgent())
        if self.config.agents.miner.enabled:
            self.agents.append(MinerAgent())
        if self.config.agents.formalizer.enabled:
            self.agents.append(FormalizerAgent())
        if self.config.agents.critic.enabled:
            self.agents.append(CriticAgent())
        
        print(f"[SUPERVISOR] Initialized with {len(self.agents)} enabled agents")
        print(f"[SUPERVISOR] Log directory: {self.log_dir}")
        print(f"[SUPERVISOR] Offline mode: {self.offline}")
        print(f"[SUPERVISOR] Cost guard: {self.config.cost.enabled}")
        print(f"[SUPERVISOR] Max spend: ${self.config.cost.max_monthly_spend}")
    
    def log_to_jsonl(self, log_entry: Dict[str, Any]) -> None:
        """
        Write log entry to JSONL file.
        
        Args:
            log_entry: Dictionary to log
        """
        # Create log file path with run_id
        run_id = log_entry.get("run_id", "unknown")
        log_file = self.log_dir / f"{run_id}.jsonl"
        
        # Append to JSONL file
        with open(log_file, "a") as f:
            f.write(json.dumps(log_entry) + "\n")
    
    def load_plan(self, plan_path: Path) -> Dict[str, Any]:
        """
        Load execution plan from YAML file.
        
        Args:
            plan_path: Path to YAML plan file
        
        Returns:
            Dictionary with plan configuration
        """
        print(f"[SUPERVISOR] Loading plan from {plan_path}")
        
        with open(plan_path, "r") as f:
            plan = yaml.safe_load(f)
        
        print(f"[SUPERVISOR] Plan loaded: {plan.get('name', 'unnamed')}")
        return plan
    
    def create_context(
        self,
        run_id: str,
        seed: int,
        config: Dict[str, Any],
    ) -> AgentContext:
        """
        Create execution context for agent pipeline.
        
        Args:
            run_id: Unique identifier for this run
            seed: Random seed for determinism
            config: Configuration dictionary
        
        Returns:
            AgentContext for agent execution
        """
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        
        context = AgentContext(
            run_id=run_id,
            seed=seed,
            timestamp=timestamp,
            config=config,
            artifacts={},
            log_callback=self.log_to_jsonl,
        )
        
        return context
    
    def execute_pipeline(
        self,
        plan: Optional[Dict[str, Any]] = None,
        seed: int = 42,
    ) -> Dict[str, Any]:
        """
        Execute full agent pipeline.
        
        Args:
            plan: Optional execution plan (uses self.config if None)
            seed: Random seed for determinism
        
        Returns:
            Dictionary with execution summary and results
        """
        # Generate unique run ID
        run_id = str(uuid.uuid4())[:8]
        
        print("=" * 60)
        print(f"[SUPERVISOR] Starting pipeline execution")
        print(f"[SUPERVISOR] Run ID: {run_id}")
        print(f"[SUPERVISOR] Seed: {seed}")
        print("=" * 60)
        
        # Create execution context
        # Convert config to dict for context
        config_dict = self.config.dict() if hasattr(self.config, 'dict') else self.config
        
        if plan is not None:
            # Merge plan into config
            config_dict = {**config_dict, **plan}
        
        context = self.create_context(run_id, seed, config_dict)
        
        # Log run start
        self.log_to_jsonl({
            "timestamp": context.timestamp,
            "run_id": run_id,
            "event": "pipeline_start",
            "seed": seed,
            "config": config_dict,
        })
        
        # Execute agents in sequence
        results = {}
        start_time = time.time()
        
        for agent in self.agents:
            print(f"\n[SUPERVISOR] Executing agent: {agent.name}")
            
            # Execute agent
            result = agent.execute(context)
            
            # Store result
            results[agent.name] = result
            
            # Store artifacts for next agents
            context.artifacts[agent.name] = result.artifacts
            
            # Log result
            self.log_to_jsonl({
                "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
                "run_id": run_id,
                "event": "agent_complete",
                "agent": agent.name,
                "result": result.to_dict(),
            })
            
            print(f"[SUPERVISOR] {agent.name} completed with status: {result.status}")
        
        # Calculate total time
        total_time = time.time() - start_time
        
        # Log pipeline completion
        self.log_to_jsonl({
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "run_id": run_id,
            "event": "pipeline_complete",
            "total_time_seconds": total_time,
            "num_agents": len(self.agents),
        })
        
        print("=" * 60)
        print(f"[SUPERVISOR] Pipeline complete in {total_time:.3f}s")
        print(f"[SUPERVISOR] Logs: {self.log_dir / f'{run_id}.jsonl'}")
        print("=" * 60)
        
        # Build summary
        summary = {
            "run_id": run_id,
            "seed": seed,
            "total_time_seconds": total_time,
            "agents": {
                name: {
                    "status": result.status,
                    "duration": result.duration_seconds,
                    "metrics": result.metrics,
                }
                for name, result in results.items()
            },
            "log_file": str(self.log_dir / f"{run_id}.jsonl"),
        }
        
        return summary
    
    def run_from_plan_file(self, plan_path: Path) -> Dict[str, Any]:
        """
        Load plan from file and execute pipeline.
        
        Args:
            plan_path: Path to YAML plan file
        
        Returns:
            Execution summary
        """
        plan = self.load_plan(plan_path)
        seed = plan.get("seed", 42)
        
        return self.execute_pipeline(plan=plan, seed=seed)


def main():
    """
    Main entry point for standalone supervisor execution.
    """
    import argparse
    
    parser = argparse.ArgumentParser(description="Run SATurday agent supervisor")
    parser.add_argument(
        "--plan",
        type=Path,
        help="Path to YAML plan file"
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="Random seed (default: 42)"
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        default=True,
        help="Enforce offline mode (default: True)"
    )
    
    args = parser.parse_args()
    
    # Create supervisor (will load default config)
    supervisor = Supervisor()
    
    # Execute pipeline
    if args.plan:
        summary = supervisor.run_from_plan_file(args.plan)
    else:
        summary = supervisor.execute_pipeline(seed=args.seed)
    
    # Print summary
    print("\n=== Execution Summary ===")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

