"""
Metrics collection and aggregation for benchmark runs.

Tracks timing, success rates, and artifact metadata across test instances.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional
import time


@dataclass
class AgentMetrics:
    """Metrics for a single agent execution.
    
    Attributes:
        agent_name: Name of the agent
        start_time: Execution start timestamp
        end_time: Execution end timestamp
        success: Whether execution succeeded
        error_message: Error message if failed
        metadata: Additional agent-specific metadata
    """
    agent_name: str
    start_time: float
    end_time: float
    success: bool
    error_message: Optional[str] = None
    metadata: Dict = field(default_factory=dict)
    
    @property
    def duration(self) -> float:
        """Calculate execution duration in seconds."""
        return self.end_time - self.start_time


@dataclass
class InstanceMetrics:
    """Metrics for a complete test instance execution.
    
    Attributes:
        instance_id: Unique identifier for test instance
        config: Test instance configuration
        start_time: Instance start timestamp
        end_time: Instance end timestamp
        agent_metrics: Per-agent execution metrics
        artifacts: Artifact hashes produced
        success: Overall success status
    """
    instance_id: str
    config: Dict
    start_time: float
    end_time: Optional[float] = None
    agent_metrics: List[AgentMetrics] = field(default_factory=list)
    artifacts: Dict[str, str] = field(default_factory=dict)
    success: bool = False
    
    @property
    def duration(self) -> float:
        """Calculate total instance duration in seconds."""
        if self.end_time is None:
            return time.time() - self.start_time
        return self.end_time - self.start_time
    
    def add_agent_result(
        self,
        agent_name: str,
        start: float,
        end: float,
        success: bool,
        error: Optional[str] = None,
        metadata: Optional[Dict] = None,
    ) -> None:
        """Add agent execution result to instance metrics.
        
        Args:
            agent_name: Name of the agent
            start: Start timestamp
            end: End timestamp
            success: Whether execution succeeded
            error: Error message if failed
            metadata: Additional metadata
        """
        metrics = AgentMetrics(
            agent_name=agent_name,
            start_time=start,
            end_time=end,
            success=success,
            error_message=error,
            metadata=metadata or {},
        )
        self.agent_metrics.append(metrics)
    
    def get_agent_duration(self, agent_name: str) -> Optional[float]:
        """Get duration for specific agent.
        
        Args:
            agent_name: Name of agent
            
        Returns:
            Optional[float]: Duration in seconds, or None if not found
        """
        for metrics in self.agent_metrics:
            if metrics.agent_name == agent_name:
                return metrics.duration
        return None
    
    def get_agent_success(self, agent_name: str) -> Optional[bool]:
        """Get success status for specific agent.
        
        Args:
            agent_name: Name of agent
            
        Returns:
            Optional[bool]: Success status, or None if not found
        """
        for metrics in self.agent_metrics:
            if metrics.agent_name == agent_name:
                return metrics.success
        return None


@dataclass
class BenchmarkMetrics:
    """Aggregate metrics for entire benchmark run.
    
    Attributes:
        run_id: Unique benchmark run identifier
        start_time: Benchmark start timestamp
        end_time: Benchmark end timestamp
        instance_metrics: Metrics for each test instance
        baseline_path: Path to baseline CSV for comparison (optional)
    """
    run_id: str
    start_time: float
    end_time: Optional[float] = None
    instance_metrics: List[InstanceMetrics] = field(default_factory=list)
    baseline_path: Optional[str] = None
    
    @property
    def duration(self) -> float:
        """Calculate total benchmark duration in seconds."""
        if self.end_time is None:
            return time.time() - self.start_time
        return self.end_time - self.start_time
    
    @property
    def total_instances(self) -> int:
        """Count total test instances."""
        return len(self.instance_metrics)
    
    @property
    def successful_instances(self) -> int:
        """Count successful test instances."""
        return sum(1 for m in self.instance_metrics if m.success)
    
    @property
    def failed_instances(self) -> int:
        """Count failed test instances."""
        return self.total_instances - self.successful_instances
    
    @property
    def success_rate(self) -> float:
        """Calculate success rate as percentage."""
        if self.total_instances == 0:
            return 0.0
        return (self.successful_instances / self.total_instances) * 100.0
    
    def get_agent_stats(self, agent_name: str) -> Dict:
        """Get aggregated statistics for specific agent.
        
        Args:
            agent_name: Name of agent
            
        Returns:
            Dict: Statistics including success rate, avg duration, etc.
        """
        durations = []
        successes = 0
        total = 0
        
        for instance in self.instance_metrics:
            for agent_metric in instance.agent_metrics:
                if agent_metric.agent_name == agent_name:
                    total += 1
                    durations.append(agent_metric.duration)
                    if agent_metric.success:
                        successes += 1
        
        if total == 0:
            return {
                'total': 0,
                'successes': 0,
                'failures': 0,
                'success_rate': 0.0,
                'avg_duration': 0.0,
                'min_duration': 0.0,
                'max_duration': 0.0,
            }
        
        return {
            'total': total,
            'successes': successes,
            'failures': total - successes,
            'success_rate': (successes / total) * 100.0,
            'avg_duration': sum(durations) / len(durations),
            'min_duration': min(durations),
            'max_duration': max(durations),
        }
    
    def get_circuit_type_stats(self, circuit_type: str) -> Dict:
        """Get aggregated statistics for specific circuit type.
        
        Args:
            circuit_type: Circuit type (monotone, ac0, formula)
            
        Returns:
            Dict: Statistics for that circuit type
        """
        instances = [
            m for m in self.instance_metrics
            if m.config.get('circuit_type') == circuit_type
        ]
        
        if not instances:
            return {
                'total': 0,
                'successes': 0,
                'failures': 0,
                'success_rate': 0.0,
                'avg_duration': 0.0,
            }
        
        successes = sum(1 for m in instances if m.success)
        durations = [m.duration for m in instances]
        
        return {
            'total': len(instances),
            'successes': successes,
            'failures': len(instances) - successes,
            'success_rate': (successes / len(instances)) * 100.0,
            'avg_duration': sum(durations) / len(durations),
        }
    
    def to_summary_dict(self) -> Dict:
        """Convert metrics to summary dictionary.
        
        Returns:
            Dict: Summary statistics
        """
        return {
            'run_id': self.run_id,
            'duration': self.duration,
            'total_instances': self.total_instances,
            'successful_instances': self.successful_instances,
            'failed_instances': self.failed_instances,
            'success_rate': self.success_rate,
        }
