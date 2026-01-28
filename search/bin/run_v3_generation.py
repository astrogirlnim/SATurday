#!/usr/bin/env python3
"""
V3 Generation Script - Multi-function, multi-circuit systematic generation
Executes comprehensive bet A stage 1 with:
- Circuit types: monotone, AC0, formula
- Functions: parity, majority, threshold-2, threshold-3
- Sizes: n=6-10
- Seeds: 3 per configuration

Total expected: 3 circuit_types × 4 functions × 5 sizes × 3 seeds = 180 instances
"""
import subprocess
import sys
import json
import time
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Any

# Configuration
CONFIG_FILE = "infra/config/bet_a_stage1.yaml"
REPORT_DIR = Path("docs/reports/v3_generation")
LOG_FILE = Path("search/logs/v3_generation_batch.jsonl")

def main():
    """Execute V3 generation batch."""
    print("=" * 80)
    print("V3 Generation: Systematic Bet A Coverage")
    print("=" * 80)
    print(f"Configuration: {CONFIG_FILE}")
    print(f"Expected output: ~180 instances")
    print(f"  - Circuit types: monotone, AC0, formula")
    print(f"  - Functions: parity, majority, threshold-2, threshold-3")
    print(f"  - Sizes: n=6-10")
    print(f"  - Seeds: 3 per configuration")
    print("=" * 80)
    print()
    
    # Create output directories
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    
    # Initialize results log
    results: List[Dict[str, Any]] = []
    
    start_time = datetime.now()
    
    # Single supervisor run with planner generating all tasks
    print("[V3] Starting supervisor pipeline with comprehensive config...")
    print()
    
    # Build command - supervisor will use planner to generate all tasks
    # Use venv Python to ensure dependencies are available
    venv_python = Path("venv/bin/python")
    python_exe = str(venv_python) if venv_python.exists() else sys.executable
    
    cmd = [
        python_exe,
        "-m", "search.cli",
        "mine",
        "--bet", "A",
        "--config", CONFIG_FILE,
        "--report",
        "--offline"
    ]
    
    print(f"[V3] Command: {' '.join(cmd)}")
    print()
    
    # Execute
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=3600,  # 1 hour max for full run
            cwd=Path.cwd()
        )
        
        # Parse result
        success = result.returncode == 0
        
        # Print output
        print(result.stdout)
        if result.stderr:
            print("STDERR:", result.stderr, file=sys.stderr)
        
        # Log result
        result_data = {
            "success": success,
            "returncode": result.returncode,
            "timestamp": datetime.now().isoformat(),
            "stdout_length": len(result.stdout),
            "stderr_length": len(result.stderr),
        }
        
        results.append(result_data)
        
        # Write result to log
        with LOG_FILE.open("w") as f:
            f.write(json.dumps(result_data, indent=2) + "\n")
        
        if not success:
            print()
            print("=" * 80)
            print("EXECUTION FAILED")
            print("=" * 80)
            print(f"Exit code: {result.returncode}")
            return 1
        
    except subprocess.TimeoutExpired:
        print()
        print("=" * 80)
        print("EXECUTION TIMEOUT")
        print("=" * 80)
        results.append({
            "success": False,
            "timeout": True,
            "timestamp": datetime.now().isoformat(),
        })
        return 1
    except Exception as e:
        print()
        print("=" * 80)
        print("EXECUTION ERROR")
        print("=" * 80)
        print(f"Error: {e}")
        results.append({
            "success": False,
            "exception": str(e),
            "timestamp": datetime.now().isoformat(),
        })
        return 1
    
    end_time = datetime.now()
    duration = end_time - start_time
    
    # Summary
    print()
    print("=" * 80)
    print("V3 Generation Complete")
    print("=" * 80)
    print(f"Duration: {duration}")
    print(f"Log: {LOG_FILE}")
    print()
    
    # Count generated artifacts
    print("Checking generated artifacts...")
    proofs_dir = Path("proofs")
    theory_conj_dir = Path("theory/Conjectures")
    
    if proofs_dir.exists():
        cnf_files = list(proofs_dir.glob("*.cnf"))
        lrat_files = list(proofs_dir.glob("*.lrat"))
        print(f"  CNF files: {len(cnf_files)}")
        print(f"  LRAT proofs: {len(lrat_files)}")
    
    if theory_conj_dir.exists():
        lean_files = list(theory_conj_dir.glob("**/*.lean"))
        print(f"  Lean stubs: {len(lean_files)}")
    
    print()
    print("=" * 80)
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
