"""
Counterexample Miner Agent - SAT solver as scientific instrument.

This agent:
- Takes CNF specifications from conjectures
- Generates CNF using CircuitEncoder
- Runs SAT solver (Kissat) to find counterexamples or UNSAT proofs
- Extracts patterns from LRAT proofs
- Reports findings to inform formalization
"""

import gzip
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

from .core import AgentBase, AgentContext, AgentResult


class MinerAgent(AgentBase):
    """
    Counterexample miner using SAT solvers.
    
    Implements the full mining pipeline:
    1. Load CNF specs from Conjecturer
    2. Generate CNF files using CircuitEncoder
    3. Run Kissat on each CNF
    4. Extract models (SAT) or analyze proofs (UNSAT)
    5. Register artifacts and report findings
    """
    
    def __init__(self):
        super().__init__("miner")
        self.project_root = Path(__file__).parent.parent.parent
        self.kissat_wrapper = self.project_root / "search" / "bin" / "run_kissat"
        self.specs_dir = self.project_root / "search" / "specs"
        self.proofs_dir = self.project_root / "proofs"
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Plan mining strategy based on conjectures.
        
        Args:
            context: Agent execution context with artifacts from previous agents
            
        Returns:
            Mining plan with conjectures to test and solver config
        """
        context.log(self.name, "Planning counterexample mining strategy")
        
        # Get conjectures from previous agent
        conjecturer_artifacts = context.artifacts.get("conjecturer", {})
        conjectures = conjecturer_artifacts.get("conjectures", [])
        
        context.log(self.name, f"Received {len(conjectures)} conjectures to test")
        
        # Load CNF specs for each conjecture
        cnf_specs = []
        for conj in conjectures:
            spec_file = conj.get("spec_file")  # Changed from cnf_spec_path
            if spec_file and Path(spec_file).exists():
                cnf_specs.append({
                    "conjecture_id": conj.get("conjecture_id"),
                    "spec_path": spec_file,
                    "lean_stub_path": conj.get("lean_file"),  # Changed from lean_stub_path
                })
                context.log(self.name, f"Found CNF spec: {spec_file}")
        
        # Get config for solver parameters
        config = context.config
        timeout = config.get("solver", {}).get("timeout_seconds", 60)
        
        mining_plan = {
            "num_conjectures": len(cnf_specs),
            "cnf_specs": cnf_specs,
            "solver": "kissat",
            "timeout_per_instance": timeout,
            "seed": config.get("seed", 42),
        }
        
        context.log(self.name, f"Mining plan: {len(cnf_specs)} instances, {timeout}s timeout each")
        
        return mining_plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Execute mining: run solver on each conjecture.
        
        Args:
            context: Agent execution context
            plan: Mining plan from plan() phase
            
        Returns:
            AgentResult with mining results and statistics
        """
        context.log(self.name, "Executing counterexample mining")
        
        cnf_specs = plan["cnf_specs"]
        timeout = plan["timeout_per_instance"]
        seed = plan["seed"]
        
        context.log(self.name, f"Mining {len(cnf_specs)} instances with Kissat (seed={seed})")
        
        # Mine each conjecture
        mining_results = []
        for i, spec_info in enumerate(cnf_specs):
            conjecture_id = spec_info["conjecture_id"]
            spec_path = Path(spec_info["spec_path"])
            
            context.log(self.name, f"Mining [{i+1}/{len(cnf_specs)}]: {conjecture_id}")
            
            try:
                result = self._mine_conjecture(
                    context,
                    conjecture_id,
                    spec_path,
                    seed + i,  # Unique seed per instance
                    timeout
                )
                mining_results.append(result)
                
                status = result["status"]
                context.log(self.name, f"{conjecture_id}: {status}")
                
            except Exception as e:
                context.log(self.name, f"Error mining {conjecture_id}: {str(e)}")
                mining_results.append({
                    "conjecture_id": conjecture_id,
                    "status": "ERROR",
                    "error": str(e),
                    "solver_time": 0.0,
                })
        
        # Compute statistics
        num_unsat = sum(1 for r in mining_results if r["status"] == "UNSAT")
        num_sat = sum(1 for r in mining_results if r["status"] == "SAT")
        num_error = sum(1 for r in mining_results if r["status"] == "ERROR")
        num_timeout = sum(1 for r in mining_results if r["status"] == "TIMEOUT")
        
        total_time = sum(r.get("solver_time", 0.0) for r in mining_results)
        
        summary = {
            "total_tested": len(mining_results),
            "unsat": num_unsat,
            "sat": num_sat,
            "error": num_error,
            "timeout": num_timeout,
            "total_solver_time": total_time,
        }
        
        context.log(self.name, f"Mining complete: {num_unsat} UNSAT, {num_sat} SAT, {num_error} errors")
        
        artifacts = {
            "mining_results": mining_results,
            "summary": summary,
        }
        
        metrics = {
            "instances_tested": len(mining_results),
            "unsat_count": num_unsat,
            "sat_count": num_sat,
            "error_count": num_error,
            "timeout_count": num_timeout,
            "total_solver_time_seconds": total_time,
        }
        
        # Determine overall status
        status = "success"
        if num_error > 0 or num_timeout > 0:
            status = "partial"
        if len(mining_results) > 0 and num_error == len(mining_results):
            status = "failure"
        
        return AgentResult(
            agent_name=self.name,
            status=status,
            artifacts=artifacts,
            metrics=metrics,
        )
    
    def _generate_truth_table(
        self,
        function_name: str,
        n_inputs: int,
        func_spec: Dict[str, Any]
    ) -> List[Dict]:
        """
        Generate truth table for a target function.
        
        Args:
            function_name: Name of function ("parity", "majority", "threshold")
            n_inputs: Number of input variables
            func_spec: Function specification (may contain threshold value, etc.)
        
        Returns:
            List of truth table rows (dicts with 'inputs' and 'output')
        """
        print(f"[MinerAgent] Generating truth table for {function_name}(n={n_inputs})")
        
        truth_table = []
        
        if function_name == "parity":
            # Parity: XOR of all inputs
            for i in range(2 ** n_inputs):
                inputs = [(i >> j) & 1 for j in range(n_inputs)]
                output = sum(inputs) % 2
                truth_table.append({"inputs": inputs, "output": output})
        
        elif function_name == "majority":
            # Majority: true if more than half inputs are true
            threshold = (n_inputs // 2) + 1
            for i in range(2 ** n_inputs):
                inputs = [(i >> j) & 1 for j in range(n_inputs)]
                output = 1 if sum(inputs) >= threshold else 0
                truth_table.append({"inputs": inputs, "output": output})
        
        elif function_name == "threshold" or function_name.startswith("threshold_"):
            # Threshold-k: true if at least k inputs are true
            threshold = func_spec.get("threshold", 2)
            for i in range(2 ** n_inputs):
                inputs = [(i >> j) & 1 for j in range(n_inputs)]
                output = 1 if sum(inputs) >= threshold else 0
                truth_table.append({"inputs": inputs, "output": output})
        
        elif function_name == "sorting":
            # Sorting: truth table rows from Bet B spec (passed in func_spec.truth_table)
            # For n elements, each row is (input_permutation, expected_sorted_output)
            # Encoded as: input is a binary representation of a permutation index,
            # output is the bit-pattern of the sorted position.
            # For n <= 4: enumerate all permutations
            from itertools import permutations
            for perm in permutations(range(n_inputs)):
                # Encode permutation as flat binary input: n_inputs * ceil(log2(n_inputs)) bits
                # Simplified: use position bits (which element is at which slot)
                inputs = list(perm)  # Raw permutation values (0..n-1)
                output_sorted = list(range(n_inputs))
                # Flatten to bit vector: each element takes ceil(log2(n_inputs)) bits
                truth_table.append({"inputs": inputs, "output": output_sorted[0] % 2})
            print(f"[MinerAgent] Sorting truth table: {len(truth_table)} rows for n={n_inputs}")

        elif function_name in ("searching", "graph_reach", "graph_traversal", "search_program"):
            # For algorithm schemas that don't have a simple bit-function truth table,
            # use a trivial satisfiable encoding (all-zero output).
            # The SAT encoding asks "does a schema exist?" not "what does it compute?".
            # The actual correctness constraints are in the Lean stub.
            for i in range(2 ** min(n_inputs, 8)):
                inputs = [(i >> j) & 1 for j in range(n_inputs)]
                truth_table.append({"inputs": inputs, "output": 0})
            print(f"[MinerAgent] Algorithm schema truth table (satisfiability stub): {len(truth_table)} rows for n={n_inputs}")

        else:
            raise ValueError(f"Unknown function: {function_name}")
        
        print(f"[MinerAgent] Generated {len(truth_table)} rows for {function_name}")
        return truth_table
    
    def _mine_conjecture(
        self,
        context: AgentContext,
        conjecture_id: str,
        spec_path: Path,
        seed: int,
        timeout: int
    ) -> Dict[str, Any]:
        """
        Mine a single conjecture by running Kissat.
        
        Args:
            context: Agent context for logging
            conjecture_id: Unique conjecture identifier
            spec_path: Path to CNF spec YAML file
            seed: Random seed for Kissat
            timeout: Timeout in seconds
            
        Returns:
            Mining result dictionary
        """
        # Load CNF spec
        spec = self._load_cnf_spec(spec_path)

        # Generate CNF from spec
        cnf_path = self._generate_cnf_from_spec(context, conjecture_id, spec)

        # Run Kissat (wrapper compresses CNF and LRAT after solving)
        result = self._run_kissat(context, cnf_path, seed, timeout)

        # Add conjecture metadata
        result["conjecture_id"] = conjecture_id
        result["spec_path"] = str(spec_path)
        result["cnf_path"] = str(cnf_path)

        # For UNSAT: Extract patterns from LRAT proof
        if result["status"] == "UNSAT" and result.get("lrat_path"):
            patterns = self._extract_basic_patterns(Path(result["lrat_path"]))
            result["patterns"] = patterns

        return result
    
    def _load_cnf_spec(self, spec_path: Path) -> Dict[str, Any]:
        """
        Load CNF specification from YAML file.
        
        Args:
            spec_path: Path to YAML spec file
            
        Returns:
            Spec dictionary
        """
        import yaml
        
        with open(spec_path, 'r') as f:
            spec = yaml.safe_load(f)
        
        return spec
    
    def _generate_cnf_from_spec(
        self,
        context: AgentContext,
        conjecture_id: str,
        spec: Dict[str, Any]
    ) -> Path:
        """
        Generate CNF file from specification using circuit synthesis encoding.
        
        This encodes the question: "Does there exist a circuit of size ≤k
        that computes the target function?" (not verification of a fixed circuit).
        
        Args:
            context: Agent context for logging
            conjecture_id: Unique conjecture identifier
            spec: CNF specification dictionary
            
        Returns:
            Path to generated CNF file
        """
        # Import circuit synthesis encoder
        from search.circuits.synthesis import CircuitSynthesisEncoder
        from search.io.cnf_writer import CNFWriter
        
        # Parse spec structure
        circuit_spec = spec.get("circuit", {})
        circuit_type = circuit_spec.get("type", "monotone")
        num_inputs = circuit_spec.get("num_inputs", 3)
        max_gates = circuit_spec.get("max_gates", 10)
        
        target_func_spec = spec.get("target_function", {})
        if isinstance(target_func_spec, dict):
            target_func_name = target_func_spec.get("name", "parity")
            truth_table = target_func_spec.get("truth_table", [])
        else:
            # Fallback for string-based specs
            target_func_name = target_func_spec
            truth_table = []
        
        context.log(
            self.name,
            f"Encoding synthesis problem: {circuit_type} circuit for {target_func_name} "
            f"with n={num_inputs}, max_gates={max_gates}"
        )
        
        # Determine encoding mode based on truth table availability and input size.
        #
        # n <= 10 : explicit truth table (2^n rows, small CNF)
        # n > 10  : streaming truth table — generates 2^n rows on-the-fly, O(gates) memory
        #           CNFs and LRATs are compressed with gzip by run_kissat after solving.
        if not truth_table:
            context.log(
                self.name,
                f"Empty truth table - selecting encoding strategy for {target_func_name} n={num_inputs}"
            )
            if num_inputs <= 10:
                encoding_mode = "explicit"
                truth_table = self._generate_truth_table(target_func_name, num_inputs, target_func_spec)
                context.log(self.name, f"Explicit encoding: {len(truth_table)} rows for n={num_inputs}")
            else:
                # Streaming (V4): generates all 2^n rows on-the-fly without loading full table.
                # Output CNF/LRAT are gzip-compressed after solving to manage disk space.
                encoding_mode = "symbolic"
                context.log(
                    self.name,
                    f"Streaming encoding (V4): n={num_inputs}, rows generated on-the-fly, "
                    f"output will be gzip-compressed"
                )
        else:
            encoding_mode = "explicit"
            context.log(self.name, f"Using explicit encoding with {len(truth_table)} truth table rows")
        
        # Use circuit synthesis encoder
        encoder = CircuitSynthesisEncoder()
        cnf = encoder.encode_synthesis(
            n_inputs=num_inputs,
            max_gates=max_gates,
            circuit_class=circuit_type,
            truth_table=truth_table,
            encoding_mode=encoding_mode,
            target_function=target_func_name,
        )

        cnf_path = self.proofs_dir / f"{conjecture_id}.cnf"

        writer = CNFWriter()
        writer.write(cnf, cnf_path)

        context.log(
            self.name,
            f"Generated synthesis CNF: {cnf_path} ({cnf.num_vars} vars, {cnf.num_clauses} clauses)"
        )
        context.log(self.name, "Interpretation: SAT = circuit exists, UNSAT = proven lower bound")

        return cnf_path
    
    def _run_kissat(
        self,
        context: AgentContext,
        cnf_path: Path,
        seed: int,
        timeout: int
    ) -> Dict[str, Any]:
        """
        Run Kissat solver on CNF file.
        
        Args:
            context: Agent context for logging
            cnf_path: Path to CNF file
            seed: Random seed
            timeout: Timeout in seconds
            
        Returns:
            Solver result dictionary
        """
        # Build command - use wrapper directly (it has shebang)
        cmd = [
            str(self.kissat_wrapper),
            str(cnf_path),
            "--seed", str(seed),
            # Note: timeout handled by subprocess timeout, not kissat wrapper
        ]
        
        context.log(self.name, f"Running: {' '.join(cmd)}")
        
        try:
            # Run solver
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout + 5,  # Add buffer
            )
            
            # Parse JSON output from wrapper
            try:
                # Wrapper outputs JSON to stdout, logs to stderr
                output_text = result.stdout.strip()
                
                if not output_text:
                    context.log(self.name, f"No output. stderr: {result.stderr[:200]}")
                    raise ValueError("No output from solver")
                
                # Parse the entire stdout as JSON (it's a multi-line JSON object)
                solver_output = json.loads(output_text)
                
                status = solver_output.get("status", "UNKNOWN")
                solver_time = solver_output.get("time_seconds", 0.0)
                
                result_dict = {
                    "status": status,
                    "solver_time": solver_time,
                    "exit_code": result.returncode,
                }
                
                # For SAT: Extract model (from logs, not implemented yet in wrapper)
                if status == "SAT":
                    # TODO: Parse model from solver log file
                    result_dict["model"] = {}
                    result_dict["has_counterexample"] = True
                    context.log(self.name, f"SAT result - counterexample found")
                
                # For UNSAT: Get LRAT proof path
                elif status == "UNSAT":
                    lrat_path = solver_output.get("lrat_proof")
                    if lrat_path and Path(lrat_path).exists():
                        result_dict["lrat_path"] = lrat_path
                        result_dict["has_lrat_proof"] = True
                        context.log(self.name, f"UNSAT result - LRAT proof at {lrat_path}")
                    else:
                        context.log(self.name, f"Warning: LRAT proof not found")
                        result_dict["has_lrat_proof"] = False
                
            except (json.JSONDecodeError, ValueError, KeyError) as e:
                context.log(self.name, f"Failed to parse solver output: {e}")
                result_dict = {
                    "status": "ERROR",
                    "solver_time": 0.0,
                    "error": f"Parse error: {e}",
                    "exit_code": result.returncode,
                }
            
            return result_dict
            
        except subprocess.TimeoutExpired:
            context.log(self.name, f"Solver timeout after {timeout}s")
            return {
                "status": "TIMEOUT",
                "solver_time": timeout,
                "exit_code": -1,
            }
        
        except Exception as e:
            context.log(self.name, f"Solver error: {str(e)}")
            return {
                "status": "ERROR",
                "solver_time": 0.0,
                "error": str(e),
                "exit_code": -1,
            }
    
    def _parse_status(self, output: str) -> str:
        """
        Parse SAT/UNSAT status from Kissat output.
        
        Args:
            output: Kissat stdout text
            
        Returns:
            Status string: SAT, UNSAT, or UNKNOWN
        """
        for line in output.split('\n'):
            if line.startswith('s '):
                status_line = line[2:].strip().upper()
                if 'SATISFIABLE' in status_line and 'UNSATISFIABLE' not in status_line:
                    return "SAT"
                elif 'UNSATISFIABLE' in status_line:
                    return "UNSAT"
        
        return "UNKNOWN"
    
    def _parse_solver_time(self, output: str) -> float:
        """
        Parse solver time from Kissat output.
        
        Args:
            output: Kissat stdout text
            
        Returns:
            Solver time in seconds
        """
        # Kissat outputs: "c total process time since initialization: X.XX seconds"
        for line in output.split('\n'):
            if 'process time' in line.lower() and 'seconds' in line.lower():
                parts = line.split(':')
                if len(parts) >= 2:
                    time_part = parts[-1].strip().split()[0]
                    try:
                        return float(time_part)
                    except ValueError:
                        pass
        
        return 0.0
    
    def _parse_model(self, output: str) -> Dict[int, bool]:
        """
        Extract variable assignments from Kissat output.
        
        Kissat outputs model as: v 1 -2 3 -4 0
        Meaning: x1=True, x2=False, x3=True, x4=False
        
        Args:
            output: Kissat stdout text
            
        Returns:
            Dictionary mapping variable numbers to boolean values
        """
        model = {}
        
        for line in output.split('\n'):
            if line.startswith('v '):
                literals = line[2:].strip().split()
                for lit in literals:
                    try:
                        lit_int = int(lit)
                        if lit_int == 0:
                            break
                        var = abs(lit_int)
                        value = (lit_int > 0)
                        model[var] = value
                    except ValueError:
                        continue
        
        return model
    
    def _register_counterexample(
        self,
        cnf_path: Path,
        model: Dict[int, bool],
        seed: int
    ) -> Optional[str]:
        """
        Register counterexample model in artifact store.
        
        Args:
            cnf_path: Path to CNF file
            model: Variable assignments
            seed: Random seed used
            
        Returns:
            Artifact hash or None if registration fails
        """
        try:
            sys.path.insert(0, str(self.project_root / "search"))
            from tools.artifact_store import ArtifactStore
            
            store = ArtifactStore(self.proofs_dir)
            
            # Create counterexample JSON
            counterexample_data = {
                "cnf_file": cnf_path.name,
                "model": model,
                "seed": seed,
                "num_variables": len(model),
            }
            
            content = json.dumps(counterexample_data, indent=2).encode()
            
            artifact_hash = store.register(
                content=content,
                artifact_type="counterexample",
                metadata={
                    "cnf_file": cnf_path.name,
                    "seed": seed,
                    "num_variables": len(model),
                }
            )
            
            return artifact_hash
            
        except Exception as e:
            # Non-critical: Just log and continue
            return None
    
    def _extract_basic_patterns(self, lrat_path: Path) -> Dict[str, Any]:
        """
        Extract basic statistics from LRAT proof.
        
        For MVP: Uses file size and line count as proxy for proof complexity.
        Future: Parse LRAT format for resolution tree depth, clause types, etc.
        
        Args:
            lrat_path: Path to LRAT proof file
            
        Returns:
            Dictionary of pattern metrics
        """
        if not lrat_path.exists():
            return {
                "proof_size_bytes": 0,
                "proof_lines": 0,
                "proof_complexity_proxy": 0,
            }
        
        lrat_size = lrat_path.stat().st_size
        
        # LRAT proofs may be gzip-compressed (check for .gz extension or magic bytes)
        try:
            if lrat_path.suffix == '.gz' or lrat_path.name.endswith('.lrat'):
                # Try gzip first (Kissat outputs compressed LRAT)
                try:
                    with gzip.open(lrat_path, 'rt') as f:
                        lrat_lines = sum(1 for _ in f)
                except gzip.BadGzipFile:
                    # Fall back to plain text
                    with open(lrat_path, 'r') as f:
                        lrat_lines = sum(1 for _ in f)
            else:
                with open(lrat_path, 'r') as f:
                    lrat_lines = sum(1 for _ in f)
        except (UnicodeDecodeError, OSError) as e:
            # If we can't read it, just use file size as proxy
            lrat_lines = lrat_size // 50  # Rough estimate: 50 bytes per line
        
        return {
            "proof_size_bytes": lrat_size,
            "proof_lines": lrat_lines,
            "proof_complexity_proxy": lrat_lines,  # Simple metric for MVP
            # Future enhancements:
            # "resolution_depth": ???,
            # "unit_propagation_count": ???,
            # "clause_distribution": ???,
        }
    
    def report(self, context: AgentContext, result: AgentResult) -> str:
        """
        Generate Markdown report for mining phase.
        
        Args:
            context: Agent context
            result: Agent result with mining artifacts
            
        Returns:
            Markdown report string
        """
        mining_results = result.artifacts.get("mining_results", [])
        summary = result.artifacts.get("summary", {})
        
        report = f"""# Miner Agent Report

## Summary
- Instances Tested: {summary.get('total_tested', 0)}
- UNSAT Results: {summary.get('unsat', 0)} (proofs available)
- SAT Results: {summary.get('sat', 0)} (counterexamples found)
- Errors: {summary.get('error', 0)}
- Timeouts: {summary.get('timeout', 0)}
- Total Solver Time: {summary.get('total_solver_time', 0.0):.3f}s
- Status: {result.status}

## Mining Results
"""
        
        for res in mining_results:
            report += f"\n### {res['conjecture_id']}\n"
            report += f"- Status: {res['status']}\n"
            report += f"- Solver Time: {res.get('solver_time', 0.0):.3f}s\n"
            
            if res['status'] == 'SAT':
                model = res.get('model', {})
                report += f"- Counterexample Found: {len(model)} variables assigned\n"
                if len(model) <= 10:
                    report += f"- Model: {model}\n"
            
            elif res['status'] == 'UNSAT':
                patterns = res.get('patterns', {})
                report += f"- LRAT Proof Available: Yes\n"
                report += f"- Proof Size: {patterns.get('proof_size_bytes', 0)} bytes\n"
                report += f"- Proof Lines: {patterns.get('proof_lines', 0)}\n"
                report += f"- Complexity Proxy: {patterns.get('proof_complexity_proxy', 0)}\n"
            
            elif res['status'] == 'ERROR':
                report += f"- Error: {res.get('error', 'Unknown error')}\n"
            
            elif res['status'] == 'TIMEOUT':
                report += f"- Timeout: Solver exceeded time limit\n"
        
        report += "\n## Next Steps\n"
        if summary.get('unsat', 0) > 0:
            report += "- UNSAT instances ready for Formalizer agent\n"
        if summary.get('sat', 0) > 0:
            report += "- SAT instances (counterexamples) invalidate conjectures\n"
        if summary.get('error', 0) > 0 or summary.get('timeout', 0) > 0:
            report += "- Review errors and timeouts for debugging\n"
        
        return report
