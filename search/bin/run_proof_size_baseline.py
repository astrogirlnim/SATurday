#!/usr/bin/env python3
"""
Budgeted proof-size baseline runner for the falsifier skill.

For one CNF family (php, tseitin, random-kcnf) and a parameter sweep, this runner:
1. Computes an exact pre-run cost estimate (vars, clauses, bytes) BEFORE generating
   anything, and refuses instances whose CNF would exceed the size cap.
2. Enforces hard wall-clock budgets from docs/p-vs-np-stop-conditions.md: a per
   instance cap and a whole-session cap. No unbounded solver runs, ever.
3. Generates the CNF deterministically, solves with the run_kissat wrapper (fixed
   seed, LRAT logging, artifact registration into proofs/index.json).
4. Measures proof size (bytes and lines, gzip aware) as calibration data.
5. Runs the verify_lrat format check where possible and labels it honestly as
   format_only (it is a stub, not a verified checker).
6. Appends one JSON line per instance plus one summary line to
   search/logs/falsifier_runs.jsonl.

Empirical results never substitute for theorems; they calibrate conjectures
(docs/p-vs-np-proof-standards.md).

Usage:
    python search/bin/run_proof_size_baseline.py --family php --n-min 4 --n-max 10 --seed 42

LOG: falsifier budgeted baseline runner
"""

import argparse
import gzip
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional

# Make the repo root importable regardless of invocation style.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

# Load the stdlib-only families module directly by path. A package import would
# trigger search/benchmarks/__init__.py, which drags in the legacy pydantic v2
# harness stack that this runner does not need.
import importlib.util

_FAMILIES_PATH = REPO_ROOT / "search" / "benchmarks" / "proof_complexity_families.py"
_spec = importlib.util.spec_from_file_location("proof_complexity_families", _FAMILIES_PATH)
families = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(families)

# Budget defaults; mirror docs/p-vs-np-stop-conditions.md. CLI can override, and
# every override is recorded in the run log line for auditability.
DEFAULT_INSTANCE_TIMEOUT_S = 1800
DEFAULT_SESSION_BUDGET_S = 3600
DEFAULT_MAX_CNF_MB = 500

RUNS_LOG = REPO_ROOT / "search" / "logs" / "falsifier_runs.jsonl"
PROOFS_DIR = REPO_ROOT / "proofs"
RUN_KISSAT = REPO_ROOT / "search" / "bin" / "run_kissat"
VERIFY_LRAT = REPO_ROOT / "search" / "bin" / "verify_lrat"


def log(message: str) -> None:
    """Timestamped stderr logging."""
    timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
    print(f"[falsifier {timestamp}] {message}", file=sys.stderr)


def append_jsonl(path: Path, record: Dict) -> None:
    """Append one JSON line; the canonical falsifier ledger is append only."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as f:
        f.write(json.dumps(record, sort_keys=True) + "\n")
    log(f"appended record to {path}")


def proof_metrics(proof_path: Optional[str]) -> Dict:
    """Measure proof size in bytes and lines; transparent for .gz files."""
    if not proof_path:
        return {"proof_bytes": None, "proof_lines": None, "proof_compressed": None}
    path = Path(proof_path)
    if not path.exists():
        return {"proof_bytes": None, "proof_lines": None, "proof_compressed": None}
    raw_bytes = path.stat().st_size
    compressed = path.suffix == ".gz"
    opener = gzip.open if compressed else open
    lines = 0
    with opener(path, "rb") as f:
        for _ in f:
            lines += 1
    log(f"proof metrics: {raw_bytes} bytes on disk, {lines} lines, compressed={compressed}")
    return {"proof_bytes": raw_bytes, "proof_lines": lines, "proof_compressed": compressed}


def format_check(cnf_path: Optional[str], proof_path: Optional[str]) -> str:
    """
    Run the verify_lrat stub where possible. Honest labeling: this is a format
    check only, not verified proof checking (see the stub's own docstring).
    """
    if not proof_path or not Path(proof_path).exists():
        return "no_proof"
    if Path(proof_path).suffix == ".gz":
        log("format check skipped: proof is compressed")
        return "skipped_compressed"
    try:
        result = subprocess.run(
            [sys.executable, str(VERIFY_LRAT), "--cnf", str(cnf_path), "--lrat", str(proof_path)],
            capture_output=True, text=True, timeout=60,
        )
        verdict = "format_only" if result.returncode == 0 else "format_check_failed"
        log(f"verify_lrat exit {result.returncode}: {verdict}")
        return verdict
    except subprocess.TimeoutExpired:
        log("verify_lrat timed out after 60 seconds")
        return "format_check_timeout"


def run_instance(
    family: str, n: int, seed: int, density: float, k: int,
    timeout_s: int, max_cnf_mb: int,
) -> Dict:
    """Estimate, budget-check, generate, solve, and measure one instance."""
    record: Dict = {
        "family": family, "n": n, "seed": seed,
        "density": density if family == "random-kcnf" else None,
        "k": k if family == "random-kcnf" else None,
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
    }

    # 1. Pre-run cost estimate, before any generation (stop-conditions rule).
    est = families.estimate(family, n, density=density, k=k)
    record.update({"est_" + key: value for key, value in est.items()})
    log(f"{family} n={n}: estimate {est['num_vars']} vars, "
        f"{est['num_clauses']} clauses, {est['est_bytes']} bytes")

    max_bytes = max_cnf_mb * 1024 * 1024
    if est["est_bytes"] > max_bytes:
        log(f"REFUSED: estimated CNF {est['est_bytes']} bytes exceeds cap {max_bytes}")
        record["status"] = "REFUSED_SIZE_CAP"
        return record

    # 2. Deterministic generation.
    num_vars, clauses = families.generate(family, n, density=density, k=k, seed=seed)
    cnf_name = f"{family.replace('-', '_')}_n{n}_seed{seed}.cnf"
    cnf_path = PROOFS_DIR / cnf_name
    written = families.write_dimacs(
        cnf_path, num_vars, clauses,
        comment=f"{family} n={n} seed={seed} density={density} k={k} falsifier baseline",
    )
    record["cnf_bytes_actual"] = written

    # 3. Budgeted solve via the policy wrapper (seeded, LRAT, artifact registry).
    log(f"solving with timeout {timeout_s} seconds")
    start = time.time()
    result = subprocess.run(
        [sys.executable, str(RUN_KISSAT), str(cnf_path),
         "--seed", str(seed), "--timeout", str(timeout_s)],
        capture_output=True, text=True,
        timeout=timeout_s + 120,  # hard backstop above the solver's own cap
    )
    elapsed = time.time() - start
    log(f"run_kissat exit code {result.returncode} in {elapsed:.1f} seconds")

    try:
        metadata = json.loads(result.stdout)
    except json.JSONDecodeError:
        log(f"ERROR: run_kissat stdout was not JSON: {result.stdout[:500]}")
        record["status"] = "WRAPPER_ERROR"
        record["wrapper_stdout_head"] = result.stdout[:500]
        return record

    record["status"] = metadata.get("status")
    record["solve_seconds"] = metadata.get("time_seconds")
    record["input_hash"] = metadata.get("input_hash")
    record["num_vars"] = metadata.get("num_variables")
    record["num_clauses"] = metadata.get("num_clauses")

    # 4. Proof size measurement (the calibration signal).
    record.update(proof_metrics(metadata.get("lrat_proof")))

    # 5. Honest proof checking label.
    if record["status"] == "UNSAT":
        record["proof_check"] = format_check(metadata.get("input_cnf"), metadata.get("lrat_proof"))
    else:
        record["proof_check"] = "not_applicable"

    return record


def summarize(results: List[Dict]) -> Dict:
    """Growth-curve reading: consecutive proof size ratios for UNSAT instances."""
    unsat = [r for r in results if r.get("status") == "UNSAT" and r.get("proof_lines")]
    ratios = []
    for prev, curr in zip(unsat, unsat[1:]):
        if prev["proof_lines"]:
            ratios.append({
                "from_n": prev["n"], "to_n": curr["n"],
                "lines_ratio": round(curr["proof_lines"] / prev["proof_lines"], 3),
            })
    for ratio in ratios:
        log(f"proof lines growth n={ratio['from_n']} to n={ratio['to_n']}: x{ratio['lines_ratio']}")
    return {
        "record_type": "summary",
        "instances": len(results),
        "unsat": len(unsat),
        "sat": sum(1 for r in results if r.get("status") == "SAT"),
        "timeouts": sum(1 for r in results if r.get("status") == "TIMEOUT"),
        "refused": sum(1 for r in results if r.get("status") == "REFUSED_SIZE_CAP"),
        "growth_ratios": ratios,
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Budgeted proof-size baseline runner")
    parser.add_argument("--family", required=True, choices=list(families.FAMILY_NAMES))
    parser.add_argument("--n-min", type=int, required=True)
    parser.add_argument("--n-max", type=int, required=True)
    parser.add_argument("--n-step", type=int, default=1)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--density", type=float, default=5.0,
                        help="clause density for random-kcnf (default 5.0, above threshold)")
    parser.add_argument("--k", type=int, default=3, help="clause width for random-kcnf")
    parser.add_argument("--instance-timeout", type=int, default=DEFAULT_INSTANCE_TIMEOUT_S)
    parser.add_argument("--session-budget", type=int, default=DEFAULT_SESSION_BUDGET_S)
    parser.add_argument("--max-cnf-mb", type=int, default=DEFAULT_MAX_CNF_MB)
    args = parser.parse_args()

    log("=" * 60)
    log(f"falsifier baseline: family={args.family} n={args.n_min}..{args.n_max} "
        f"seed={args.seed} instance_cap={args.instance_timeout}s "
        f"session_budget={args.session_budget}s cnf_cap={args.max_cnf_mb}MB")
    log("=" * 60)

    session_start = time.time()
    results: List[Dict] = []

    for n in range(args.n_min, args.n_max + 1, args.n_step):
        if args.family == "tseitin" and n % 2 != 0:
            log(f"skipping odd n={n} for tseitin (needs even n)")
            continue

        elapsed = time.time() - session_start
        remaining = args.session_budget - elapsed
        if remaining < 5:
            log(f"SESSION BUDGET EXHAUSTED after {elapsed:.0f}s; stopping sweep at n={n}")
            results.append({
                "family": args.family, "n": n, "status": "SESSION_BUDGET_EXHAUSTED",
                "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            })
            append_jsonl(RUNS_LOG, results[-1])
            break

        timeout_s = int(min(args.instance_timeout, remaining))
        log(f"--- instance n={n} (session remaining {remaining:.0f}s, cap {timeout_s}s) ---")
        record = run_instance(
            args.family, n, args.seed, args.density, args.k,
            timeout_s=timeout_s, max_cnf_mb=args.max_cnf_mb,
        )
        record["budget"] = {
            "instance_timeout_s": timeout_s,
            "session_budget_s": args.session_budget,
            "session_elapsed_s": round(time.time() - session_start, 1),
        }
        results.append(record)
        append_jsonl(RUNS_LOG, record)

        if record.get("status") == "TIMEOUT":
            log(f"instance n={n} hit the cap; stopping sweep (larger n will also time out)")
            break

    summary = summarize(results)
    summary["family"] = args.family
    summary["seed"] = args.seed
    append_jsonl(RUNS_LOG, summary)

    log("=" * 60)
    log(f"sweep complete: {summary['unsat']} UNSAT, {summary['sat']} SAT, "
        f"{summary['timeouts']} timeouts, {summary['refused']} refused")
    log("=" * 60)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
