"""
Core benchmark harness for deterministic agent pipeline testing.

Executes test matrices with fixed seeds and collects comprehensive metrics.
"""

import hashlib
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional

# Add project root to path
repo_root = Path(__file__).parent.parent.parent
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

from search.agents.supervisor import Supervisor
from search.benchmarks.config import BenchmarkConfig
from search.benchmarks.metrics import BenchmarkMetrics, InstanceMetrics
from search.benchmarks.reporters import CSVReporter, MarkdownReporter


class BenchmarkHarness:
    """Harness for running deterministic benchmarks of the agent pipeline.
    
    The harness:
    1. Loads benchmark configuration
    2. Generates test matrix (all parameter combinations)
    3. Runs agent pipeline for each instance with fixed seed
    4. Collects comprehensive metrics
    5. Generates CSV and Markdown reports
    
    Attributes:
        config: Benchmark configuration
        supervisor: Agent supervisor instance
        metrics: Collected benchmark metrics
        fail_fast: Whether to stop on first failure
        verbose: Whether to print detailed progress
    """
    
    def __init__(
        self,
        config: BenchmarkConfig,
        supervisor_config: Optional[Path] = None,
        fail_fast: bool = False,
        verbose: bool = False,
    ):
        """Initialize benchmark harness.
        
        Args:
            config: Benchmark configuration
            supervisor_config: Optional supervisor config file
            fail_fast: Stop on first failure
            verbose: Print detailed progress
        """
        self.config = config
        self.fail_fast = fail_fast
        self.verbose = verbose
        
        # Initialize supervisor
        self.supervisor = Supervisor(config_file=supervisor_config)
        
        # Generate unique run ID
        run_id = self._generate_run_id()
        
        # Initialize metrics
        self.metrics = BenchmarkMetrics(
            run_id=run_id,
            start_time=time.time(),
        )
    
    def _generate_run_id(self) -> str:
        """Generate unique run ID based on timestamp and config.
        
        Returns:
            str: Unique 8-character hex ID
        """
        timestamp = str(time.time()).encode()
        config_str = str(self.config.config.dict()).encode()
        combined = timestamp + config_str
        return hashlib.sha256(combined).hexdigest()[:8]
    
    def run(self) -> BenchmarkMetrics:
        """Execute full benchmark suite.
        
        Returns:
            BenchmarkMetrics: Collected metrics from all instances
        """
        print(f"[Benchmark] Starting run: {self.metrics.run_id}")
        print(f"[Benchmark] Config: {self.config.config.name}")
        print(f"[Benchmark] Generating test matrix...")
        
        # Generate all test instances
        instances = self.config.generate_test_instances()
        print(f"[Benchmark] Generated {len(instances)} test instances")
        print()
        
        # Run each instance
        for idx, instance_config in enumerate(instances, 1):
            print(f"[Benchmark] Running instance {idx}/{len(instances)}")
            
            try:
                instance_metrics = self._run_instance(instance_config)
                self.metrics.instance_metrics.append(instance_metrics)
                
                if instance_metrics.success:
                    print(f"[Benchmark] Instance {idx} PASSED ({instance_metrics.duration:.2f}s)")
                else:
                    print(f"[Benchmark] Instance {idx} FAILED ({instance_metrics.duration:.2f}s)")
                    if self.fail_fast:
                        print("[Benchmark] Fail-fast enabled, stopping benchmark")
                        break
            
            except Exception as e:
                print(f"[Benchmark] Instance {idx} ERROR: {e}")
                if self.fail_fast:
                    raise
            
            print()
        
        # Mark benchmark complete
        self.metrics.end_time = time.time()
        
        print(f"[Benchmark] Completed in {self.metrics.duration:.2f}s")
        print(f"[Benchmark] Success rate: {self.metrics.success_rate:.1f}% ({self.metrics.successful_instances}/{self.metrics.total_instances})")
        
        return self.metrics
    
    def _run_instance(self, instance_config: Dict) -> InstanceMetrics:
        """Run single test instance through agent pipeline.
        
        Args:
            instance_config: Test instance configuration
            
        Returns:
            InstanceMetrics: Metrics from instance execution
        """
        # Generate instance ID
        instance_id = self._generate_instance_id(instance_config)
        
        if self.verbose:
            print(f"  Instance: {instance_id}")
            print(f"  Config: {instance_config}")
        
        # Create instance metrics
        instance = InstanceMetrics(
            instance_id=instance_id,
            config=instance_config,
            start_time=time.time(),
        )
        
        try:
            # Create plan for this instance
            plan = {
                'bet': instance_config['bet'],
                'circuit_type': instance_config['circuit_type'],
                'target_function': instance_config['target_function'],
                'n': instance_config['n'],
                'seed': instance_config['seed'],
            }
            
            # Execute agent pipeline
            result = self.supervisor.execute_pipeline(
                plan=plan,
                seed=instance_config['seed']
            )
            
            # Extract metrics from result
            self._extract_agent_metrics(result, instance)
            
            # Extract artifacts
            self._extract_artifacts(result, instance)
            
            # Determine overall success
            instance.success = result.get('success', False)
        
        except Exception as e:
            print(f"  ERROR: {e}", file=sys.stderr)
            instance.success = False
            # Log error in metrics
            instance.add_agent_result(
                agent_name='supervisor',
                start=instance.start_time,
                end=time.time(),
                success=False,
                error=str(e),
            )
        
        finally:
            instance.end_time = time.time()
        
        return instance
    
    def _generate_instance_id(self, config: Dict) -> str:
        """Generate unique instance ID from configuration.
        
        Args:
            config: Instance configuration
            
        Returns:
            str: Instance ID in format: bet_circuit_func_nX_sY
        """
        return (
            f"{config['bet']}_"
            f"{config['circuit_type']}_"
            f"{config['target_function']}_"
            f"n{config['n']}_"
            f"s{config['seed']}"
        )
    
    def _extract_agent_metrics(self, result: Dict, instance: InstanceMetrics) -> None:
        """Extract per-agent metrics from pipeline result.
        
        Args:
            result: Supervisor execution result
            instance: Instance metrics to populate
        """
        # Extract agent results if available
        agent_results = result.get('agent_results', [])
        
        for agent_result in agent_results:
            agent_name = agent_result.get('agent', 'unknown')
            
            # Get timing
            start_time = agent_result.get('start_time', instance.start_time)
            end_time = agent_result.get('end_time', instance.start_time)
            
            # Get success status
            success = agent_result.get('success', False)
            
            # Get error message
            error = agent_result.get('error')
            
            # Get agent-specific metadata
            metadata = {}
            
            if agent_name == 'miner':
                metadata['result'] = agent_result.get('result', '')
            elif agent_name == 'critic':
                metadata['barrier_tags'] = agent_result.get('barrier_tags', [])
            
            # Add to instance metrics
            instance.add_agent_result(
                agent_name=agent_name,
                start=start_time,
                end=end_time,
                success=success,
                error=error,
                metadata=metadata,
            )
    
    def _extract_artifacts(self, result: Dict, instance: InstanceMetrics) -> None:
        """Extract artifact hashes from pipeline result.
        
        Args:
            result: Supervisor execution result
            instance: Instance metrics to populate
        """
        artifacts = result.get('artifacts', {})
        
        # Extract key artifact hashes
        if 'cnf_hash' in artifacts:
            instance.artifacts['cnf_hash'] = artifacts['cnf_hash']
        if 'lrat_hash' in artifacts:
            instance.artifacts['lrat_hash'] = artifacts['lrat_hash']
    
    def generate_reports(
        self,
        output_dir: Optional[Path] = None,
    ) -> Dict[str, Path]:
        """Generate CSV and Markdown reports from collected metrics.
        
        Args:
            output_dir: Output directory (uses config default if None)
            
        Returns:
            Dict[str, Path]: Paths to generated files ('csv' and 'md')
        """
        if output_dir is None:
            output_dir = Path(self.config.config.output.csv_path)
        
        output_dir = Path(output_dir)
        
        print(f"[Benchmark] Generating reports in {output_dir}")
        
        # Generate CSV report
        csv_reporter = CSVReporter(output_dir)
        csv_path = csv_reporter.generate(self.metrics)
        print(f"[Benchmark] CSV report: {csv_path}")
        
        # Generate Markdown report
        md_reporter = MarkdownReporter(output_dir)
        md_path = md_reporter.generate(self.metrics)
        print(f"[Benchmark] Markdown report: {md_path}")
        
        return {
            'csv': csv_path,
            'md': md_path,
        }
