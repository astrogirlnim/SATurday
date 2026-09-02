#!/usr/bin/env python3
"""
Bet A Stage 1 Batch Runner
Executes 100 monotone parity instances systematically across n=2-20
"""
import subprocess
import sys
import json
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Any

# Configuration
BET = "A"
N_RANGE = range(2, 21)  # n=2 to n=20
SEEDS_PER_N = 5  # 5 seeds per n value
SEED_START = 12000
CONFIG_FILE = "infra/config/bet_a_stage1.yaml"
REPORT_DIR = Path("docs/reports/bet_a_stage1")
LOG_FILE = Path("search/logs/bet_a_stage1_batch.jsonl")

def main():
    """Execute batch run of Bet A Stage 1."""
    print("=" * 80)
    print("Bet A Stage 1: Monotone Parity Baseline")
    print("=" * 80)
    print(f"Configuration:")
    print(f"  Bet: {BET}")
    print(f"  Circuit Type: Monotone")
    print(f"  Target Function: Parity")
    print(f"  Size Range: n={min(N_RANGE)} to n={max(N_RANGE)}")
    print(f"  Seeds per n: {SEEDS_PER_N}")
    print(f"  Total instances: {len(N_RANGE) * SEEDS_PER_N}")
    print(f"  Config: {CONFIG_FILE}")
    print(f"  Reports: {REPORT_DIR}")
    print("=" * 80)
    print()
    
    # Create output directories
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    
    # Initialize results log
    results: List[Dict[str, Any]] = []
    seed = SEED_START
    
    total_instances = len(N_RANGE) * SEEDS_PER_N
    completed = 0
    failed = 0
    
    start_time = datetime.now()
    
    # Execute instances
    for n in N_RANGE:
        print(f"\n[n={n}] Starting {SEEDS_PER_N} instances...")
        
        for i in range(SEEDS_PER_N):
            current_seed = seed + i
            instance_num = completed + 1
            
            print(f"  [{instance_num}/{total_instances}] n={n}, seed={current_seed}", end=" ... ")
            sys.stdout.flush()
            
            # Build command
            cmd = [
                "./venv/bin/satday",
                "mine",
                "--bet", BET,
                "--n", str(n),
                "--seed", str(current_seed),
                "--config", CONFIG_FILE,
                "--report"
            ]
            
            # Execute
            try:
                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=120,  # 2 minutes max per instance
                    cwd=Path.cwd()
                )
                
                # Parse result
                success = result.returncode == 0
                
                # Log result
                result_data = {
                    "instance_num": instance_num,
                    "n": n,
                    "seed": current_seed,
                    "success": success,
                    "returncode": result.returncode,
                    "timestamp": datetime.now().isoformat(),
                }
                
                # Try to extract mining result from output
                if success:
                    # Look for mining result in output
                    for line in result.stdout.split("\n"):
                        if "MinerAgent" in line and "result" in line.lower():
                            # Parse SAT/UNSAT from output
                            if "UNSAT" in line:
                                result_data["sat_result"] = "UNSAT"
                            elif "SAT" in line:
                                result_data["sat_result"] = "SAT"
                    
                    print(f"OK ({result_data.get('sat_result', 'UNKNOWN')})")
                    completed += 1
                else:
                    print(f"FAILED (exit {result.returncode})")
                    result_data["error"] = result.stderr[:200]  # First 200 chars of error
                    failed += 1
                
                results.append(result_data)
                
                # Write result to log
                with LOG_FILE.open("a") as f:
                    f.write(json.dumps(result_data) + "\n")
                
            except subprocess.TimeoutExpired:
                print("TIMEOUT")
                results.append({
                    "instance_num": instance_num,
                    "n": n,
                    "seed": current_seed,
                    "success": False,
                    "timeout": True,
                    "timestamp": datetime.now().isoformat(),
                })
                failed += 1
            except Exception as e:
                print(f"ERROR: {e}")
                results.append({
                    "instance_num": instance_num,
                    "n": n,
                    "seed": current_seed,
                    "success": False,
                    "exception": str(e),
                    "timestamp": datetime.now().isoformat(),
                })
                failed += 1
        
        # Update seed offset for next n
        seed += SEEDS_PER_N
    
    end_time = datetime.now()
    duration = end_time - start_time
    
    # Summary
    print("\n" + "=" * 80)
    print("Batch Execution Complete")
    print("=" * 80)
    print(f"Total instances: {total_instances}")
    print(f"Completed: {completed} ({100*completed/total_instances:.1f}%)")
    print(f"Failed: {failed} ({100*failed/total_instances:.1f}%)")
    print(f"Duration: {duration}")
    print(f"Average time per instance: {duration.total_seconds() / total_instances:.2f}s")
    print(f"\nResults logged to: {LOG_FILE}")
    print(f"Reports in: {REPORT_DIR}")
    print("=" * 80)
    
    # Write summary
    summary_file = REPORT_DIR / "batch_summary.json"
    summary = {
        "start_time": start_time.isoformat(),
        "end_time": end_time.isoformat(),
        "duration_seconds": duration.total_seconds(),
        "total_instances": total_instances,
        "completed": completed,
        "failed": failed,
        "success_rate": completed / total_instances,
        "configuration": {
            "bet": BET,
            "n_range": [min(N_RANGE), max(N_RANGE)],
            "seeds_per_n": SEEDS_PER_N,
            "seed_start": SEED_START,
        },
        "results": results
    }
    
    with summary_file.open("w") as f:
        json.dump(summary, f, indent=2)
    
    print(f"\nSummary written to: {summary_file}")
    
    return 0 if failed == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
