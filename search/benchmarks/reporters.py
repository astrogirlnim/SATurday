"""
Benchmark report generation in CSV and Markdown formats.

Generates structured output files from benchmark metrics.
"""

import csv
from datetime import datetime
from pathlib import Path
from typing import List, Optional

from search.benchmarks.metrics import BenchmarkMetrics, InstanceMetrics


class CSVReporter:
    """Generates CSV reports from benchmark metrics.
    
    CSV format includes one row per test instance with all relevant metrics.
    """
    
    HEADERS = [
        'run_id',
        'timestamp',
        'instance_id',
        'matrix_name',
        'bet',
        'circuit_type',
        'target_function',
        'n',
        'seed',
        'planner_time',
        'planner_success',
        'conjecturer_time',
        'conjecturer_success',
        'miner_time',
        'miner_success',
        'miner_result',
        'formalizer_time',
        'formalizer_success',
        'critic_time',
        'critic_success',
        'barrier_tags',
        'total_time',
        'success',
        'cnf_hash',
        'lrat_hash',
    ]
    
    def __init__(self, output_dir: Path):
        """Initialize CSV reporter.
        
        Args:
            output_dir: Directory for CSV output
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate(
        self,
        metrics: BenchmarkMetrics,
        filename: Optional[str] = None,
    ) -> Path:
        """Generate CSV report from benchmark metrics.
        
        Args:
            metrics: Benchmark metrics to report
            filename: Output filename (defaults to timestamp_runid.csv)
            
        Returns:
            Path: Path to generated CSV file
        """
        if filename is None:
            timestamp = datetime.fromtimestamp(metrics.start_time).strftime('%Y-%m-%d_%H-%M-%S')
            filename = f"{timestamp}_{metrics.run_id}.csv"
        
        output_path = self.output_dir / filename
        
        with open(output_path, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=self.HEADERS)
            writer.writeheader()
            
            for instance in metrics.instance_metrics:
                row = self._instance_to_row(metrics.run_id, instance)
                writer.writerow(row)
        
        return output_path
    
    def _instance_to_row(self, run_id: str, instance: InstanceMetrics) -> dict:
        """Convert instance metrics to CSV row.
        
        Args:
            run_id: Benchmark run ID
            instance: Instance metrics
            
        Returns:
            dict: CSV row data
        """
        config = instance.config
        
        # Get barrier tags from critic metadata
        barrier_tags = []
        for agent_metric in instance.agent_metrics:
            if agent_metric.agent_name == 'critic' and agent_metric.metadata:
                barrier_tags = agent_metric.metadata.get('barrier_tags', [])
        
        # Get miner result (SAT/UNSAT)
        miner_result = ''
        for agent_metric in instance.agent_metrics:
            if agent_metric.agent_name == 'miner' and agent_metric.metadata:
                miner_result = agent_metric.metadata.get('result', '')
        
        return {
            'run_id': run_id,
            'timestamp': datetime.fromtimestamp(instance.start_time).isoformat(),
            'instance_id': instance.instance_id,
            'matrix_name': config.get('matrix_name', ''),
            'bet': config.get('bet', ''),
            'circuit_type': config.get('circuit_type', ''),
            'target_function': config.get('target_function', ''),
            'n': config.get('n', ''),
            'seed': config.get('seed', ''),
            'planner_time': instance.get_agent_duration('planner') or 0.0,
            'planner_success': instance.get_agent_success('planner') or False,
            'conjecturer_time': instance.get_agent_duration('conjecturer') or 0.0,
            'conjecturer_success': instance.get_agent_success('conjecturer') or False,
            'miner_time': instance.get_agent_duration('miner') or 0.0,
            'miner_success': instance.get_agent_success('miner') or False,
            'miner_result': miner_result,
            'formalizer_time': instance.get_agent_duration('formalizer') or 0.0,
            'formalizer_success': instance.get_agent_success('formalizer') or False,
            'critic_time': instance.get_agent_duration('critic') or 0.0,
            'critic_success': instance.get_agent_success('critic') or False,
            'barrier_tags': ','.join(barrier_tags),
            'total_time': instance.duration,
            'success': instance.success,
            'cnf_hash': instance.artifacts.get('cnf_hash', ''),
            'lrat_hash': instance.artifacts.get('lrat_hash', ''),
        }


class MarkdownReporter:
    """Generates Markdown summary reports from benchmark metrics."""
    
    def __init__(self, output_dir: Path):
        """Initialize Markdown reporter.
        
        Args:
            output_dir: Directory for Markdown output
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate(
        self,
        metrics: BenchmarkMetrics,
        filename: Optional[str] = None,
    ) -> Path:
        """Generate Markdown report from benchmark metrics.
        
        Args:
            metrics: Benchmark metrics to report
            filename: Output filename (defaults to timestamp_runid_summary.md)
            
        Returns:
            Path: Path to generated Markdown file
        """
        if filename is None:
            timestamp = datetime.fromtimestamp(metrics.start_time).strftime('%Y-%m-%d_%H-%M-%S')
            filename = f"{timestamp}_{metrics.run_id}_summary.md"
        
        output_path = self.output_dir / filename
        
        with open(output_path, 'w') as f:
            f.write(self._generate_content(metrics))
        
        return output_path
    
    def _generate_content(self, metrics: BenchmarkMetrics) -> str:
        """Generate Markdown content from metrics.
        
        Args:
            metrics: Benchmark metrics
            
        Returns:
            str: Markdown content
        """
        lines = []
        
        # Header
        lines.append(f"# Benchmark Report: {metrics.run_id}")
        lines.append("")
        timestamp = datetime.fromtimestamp(metrics.start_time).strftime('%Y-%m-%d %H:%M:%S')
        lines.append(f"**Date:** {timestamp}")
        lines.append(f"**Duration:** {metrics.duration:.2f}s")
        lines.append("")
        
        # Executive Summary
        lines.append("## Executive Summary")
        lines.append("")
        lines.append(f"- **Total Instances:** {metrics.total_instances}")
        lines.append(f"- **Successful:** {metrics.successful_instances}")
        lines.append(f"- **Failed:** {metrics.failed_instances}")
        lines.append(f"- **Success Rate:** {metrics.success_rate:.1f}%")
        lines.append("")
        
        # Per-Agent Statistics
        lines.append("## Agent Performance")
        lines.append("")
        agent_names = ['planner', 'conjecturer', 'miner', 'formalizer', 'critic']
        
        lines.append("| Agent | Total | Successes | Failures | Success Rate | Avg Duration |")
        lines.append("|-------|-------|-----------|----------|--------------|--------------|")
        
        for agent in agent_names:
            stats = metrics.get_agent_stats(agent)
            lines.append(
                f"| {agent.capitalize()} | {stats['total']} | {stats['successes']} | "
                f"{stats['failures']} | {stats['success_rate']:.1f}% | {stats['avg_duration']:.3f}s |"
            )
        
        lines.append("")
        
        # Per-Circuit-Type Statistics
        lines.append("## Results by Circuit Type")
        lines.append("")
        
        circuit_types = set()
        for instance in metrics.instance_metrics:
            ct = instance.config.get('circuit_type')
            if ct:
                circuit_types.add(ct)
        
        if circuit_types:
            lines.append("| Circuit Type | Total | Successes | Failures | Success Rate | Avg Duration |")
            lines.append("|--------------|-------|-----------|----------|--------------|--------------|")
            
            for ct in sorted(circuit_types):
                stats = metrics.get_circuit_type_stats(ct)
                lines.append(
                    f"| {ct} | {stats['total']} | {stats['successes']} | "
                    f"{stats['failures']} | {stats['success_rate']:.1f}% | {stats['avg_duration']:.3f}s |"
                )
            
            lines.append("")
        
        # Failures Section
        failed = [m for m in metrics.instance_metrics if not m.success]
        if failed:
            lines.append("## Failed Instances")
            lines.append("")
            
            for instance in failed:
                lines.append(f"### {instance.instance_id}")
                lines.append("")
                lines.append(f"- **Configuration:** {instance.config}")
                
                # Find failed agents
                for agent_metric in instance.agent_metrics:
                    if not agent_metric.success:
                        lines.append(f"- **Failed Agent:** {agent_metric.agent_name}")
                        if agent_metric.error_message:
                            lines.append(f"- **Error:** {agent_metric.error_message}")
                
                lines.append("")
        
        # Baseline Comparison (if available)
        if metrics.baseline_path:
            lines.append("## Baseline Comparison")
            lines.append("")
            lines.append(f"Baseline: `{metrics.baseline_path}`")
            lines.append("")
            lines.append("Regression analysis not yet implemented.")
            lines.append("")
        
        return '\n'.join(lines)
