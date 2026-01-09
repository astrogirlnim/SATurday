#!/usr/bin/env python3
"""
Test script for agent supervisor.

Runs a dry cycle with stub agents to verify the pipeline works.
"""

import sys
from pathlib import Path

# Add search directory to path
sys.path.insert(0, str(Path(__file__).parent))

from agents import Supervisor


def main():
    """Run test supervisor with default configuration."""
    print("=" * 60)
    print("Testing SATurday Agent Supervisor")
    print("=" * 60)
    
    # Default test configuration
    config = {
        "bet": "A",
        "max_size": 5,
        "num_seeds": 2,
    }
    
    # Create supervisor
    supervisor = Supervisor(config=config)
    
    # Execute pipeline with fixed seed
    summary = supervisor.execute_pipeline(seed=42)
    
    # Print summary
    print("\n" + "=" * 60)
    print("Execution Summary")
    print("=" * 60)
    print(f"Run ID: {summary['run_id']}")
    print(f"Total Time: {summary['total_time_seconds']:.3f}s")
    print(f"Log File: {summary['log_file']}")
    print()
    print("Agent Results:")
    for agent_name, agent_result in summary['agents'].items():
        print(f"  - {agent_name}: {agent_result['status']} "
              f"({agent_result['duration']:.3f}s)")
    print("=" * 60)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())

