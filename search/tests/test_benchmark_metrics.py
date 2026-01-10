"""
Unit tests for benchmark metrics module.

Tests metrics collection, aggregation, and statistics.
"""

import pytest
import time

from search.benchmarks.metrics import AgentMetrics, InstanceMetrics, BenchmarkMetrics


class TestAgentMetrics:
    """Tests for AgentMetrics."""
    
    def test_create_metrics(self):
        """Test creating agent metrics."""
        start = time.time()
        end = start + 1.5
        
        metrics = AgentMetrics(
            agent_name="planner",
            start_time=start,
            end_time=end,
            success=True,
        )
        
        assert metrics.agent_name == "planner"
        assert metrics.start_time == start
        assert metrics.end_time == end
        assert metrics.success is True
        assert metrics.error_message is None
        assert metrics.metadata == {}
    
    def test_duration_calculation(self):
        """Test duration calculation."""
        start = 100.0
        end = 105.5
        
        metrics = AgentMetrics(
            agent_name="test",
            start_time=start,
            end_time=end,
            success=True,
        )
        
        assert metrics.duration == 5.5
    
    def test_with_error(self):
        """Test metrics with error message."""
        metrics = AgentMetrics(
            agent_name="test",
            start_time=100.0,
            end_time=101.0,
            success=False,
            error_message="Test error",
        )
        
        assert metrics.success is False
        assert metrics.error_message == "Test error"


class TestInstanceMetrics:
    """Tests for InstanceMetrics."""
    
    def test_create_instance(self):
        """Test creating instance metrics."""
        config = {'bet': 'A', 'n': 5, 'seed': 42}
        start = time.time()
        
        instance = InstanceMetrics(
            instance_id="test_1",
            config=config,
            start_time=start,
        )
        
        assert instance.instance_id == "test_1"
        assert instance.config == config
        assert instance.start_time == start
        assert instance.end_time is None
        assert instance.agent_metrics == []
        assert instance.artifacts == {}
        assert instance.success is False
    
    def test_add_agent_result(self):
        """Test adding agent results."""
        instance = InstanceMetrics(
            instance_id="test_1",
            config={},
            start_time=100.0,
        )
        
        instance.add_agent_result(
            agent_name="planner",
            start=100.0,
            end=101.0,
            success=True,
        )
        
        assert len(instance.agent_metrics) == 1
        assert instance.agent_metrics[0].agent_name == "planner"
        assert instance.agent_metrics[0].duration == 1.0
    
    def test_get_agent_duration(self):
        """Test retrieving agent duration."""
        instance = InstanceMetrics(
            instance_id="test_1",
            config={},
            start_time=100.0,
        )
        
        instance.add_agent_result("planner", 100.0, 101.5, True)
        instance.add_agent_result("miner", 101.5, 105.0, True)
        
        assert instance.get_agent_duration("planner") == 1.5
        assert instance.get_agent_duration("miner") == 3.5
        assert instance.get_agent_duration("unknown") is None
    
    def test_get_agent_success(self):
        """Test retrieving agent success status."""
        instance = InstanceMetrics(
            instance_id="test_1",
            config={},
            start_time=100.0,
        )
        
        instance.add_agent_result("planner", 100.0, 101.0, True)
        instance.add_agent_result("miner", 101.0, 102.0, False, error="Failed")
        
        assert instance.get_agent_success("planner") is True
        assert instance.get_agent_success("miner") is False
        assert instance.get_agent_success("unknown") is None
    
    def test_duration_calculation(self):
        """Test instance duration calculation."""
        instance = InstanceMetrics(
            instance_id="test_1",
            config={},
            start_time=100.0,
            end_time=110.0,
        )
        
        assert instance.duration == 10.0


class TestBenchmarkMetrics:
    """Tests for BenchmarkMetrics."""
    
    def test_create_benchmark(self):
        """Test creating benchmark metrics."""
        start = time.time()
        
        metrics = BenchmarkMetrics(
            run_id="test_run",
            start_time=start,
        )
        
        assert metrics.run_id == "test_run"
        assert metrics.start_time == start
        assert metrics.end_time is None
        assert metrics.instance_metrics == []
    
    def test_total_instances(self):
        """Test counting total instances."""
        metrics = BenchmarkMetrics(run_id="test", start_time=100.0)
        
        # Add some instances
        for i in range(5):
            instance = InstanceMetrics(
                instance_id=f"test_{i}",
                config={},
                start_time=100.0,
                end_time=101.0,
                success=True,
            )
            metrics.instance_metrics.append(instance)
        
        assert metrics.total_instances == 5
    
    def test_successful_instances(self):
        """Test counting successful instances."""
        metrics = BenchmarkMetrics(run_id="test", start_time=100.0)
        
        # Add successful instances
        for i in range(3):
            instance = InstanceMetrics(
                instance_id=f"success_{i}",
                config={},
                start_time=100.0,
                end_time=101.0,
                success=True,
            )
            metrics.instance_metrics.append(instance)
        
        # Add failed instances
        for i in range(2):
            instance = InstanceMetrics(
                instance_id=f"fail_{i}",
                config={},
                start_time=100.0,
                end_time=101.0,
                success=False,
            )
            metrics.instance_metrics.append(instance)
        
        assert metrics.total_instances == 5
        assert metrics.successful_instances == 3
        assert metrics.failed_instances == 2
    
    def test_success_rate(self):
        """Test success rate calculation."""
        metrics = BenchmarkMetrics(run_id="test", start_time=100.0)
        
        # 7 successful, 3 failed = 70% success rate
        for i in range(7):
            metrics.instance_metrics.append(
                InstanceMetrics(f"s{i}", {}, 100.0, 101.0, [], {}, True)
            )
        for i in range(3):
            metrics.instance_metrics.append(
                InstanceMetrics(f"f{i}", {}, 100.0, 101.0, [], {}, False)
            )
        
        assert metrics.success_rate == 70.0
    
    def test_success_rate_empty(self):
        """Test success rate with no instances."""
        metrics = BenchmarkMetrics(run_id="test", start_time=100.0)
        assert metrics.success_rate == 0.0
    
    def test_get_agent_stats(self):
        """Test aggregating agent statistics."""
        metrics = BenchmarkMetrics(run_id="test", start_time=100.0)
        
        # Create instances with planner results
        for i in range(3):
            instance = InstanceMetrics(f"test_{i}", {}, 100.0)
            instance.add_agent_result("planner", 100.0, 101.0 + i, i < 2)  # 2 success, 1 fail
            metrics.instance_metrics.append(instance)
        
        stats = metrics.get_agent_stats("planner")
        
        assert stats['total'] == 3
        assert stats['successes'] == 2
        assert stats['failures'] == 1
        assert stats['success_rate'] == pytest.approx(66.667, rel=0.01)
    
    def test_get_circuit_type_stats(self):
        """Test aggregating circuit type statistics."""
        metrics = BenchmarkMetrics(run_id="test", start_time=100.0)
        
        # Add monotone circuit instances
        for i in range(3):
            instance = InstanceMetrics(
                f"mono_{i}",
                {'circuit_type': 'monotone'},
                100.0,
                105.0,
                [],
                {},
                i < 2,  # 2 success, 1 fail
            )
            metrics.instance_metrics.append(instance)
        
        # Add ac0 circuit instances
        for i in range(2):
            instance = InstanceMetrics(
                f"ac0_{i}",
                {'circuit_type': 'ac0'},
                100.0,
                110.0,
                [],
                {},
                True,
            )
            metrics.instance_metrics.append(instance)
        
        mono_stats = metrics.get_circuit_type_stats('monotone')
        assert mono_stats['total'] == 3
        assert mono_stats['successes'] == 2
        assert mono_stats['success_rate'] == pytest.approx(66.667, rel=0.01)
        assert mono_stats['avg_duration'] == 5.0
        
        ac0_stats = metrics.get_circuit_type_stats('ac0')
        assert ac0_stats['total'] == 2
        assert ac0_stats['successes'] == 2
        assert ac0_stats['success_rate'] == 100.0
    
    def test_to_summary_dict(self):
        """Test converting to summary dictionary."""
        metrics = BenchmarkMetrics(run_id="test_run", start_time=100.0, end_time=150.0)
        
        # Add some instances
        for i in range(5):
            instance = InstanceMetrics(f"t{i}", {}, 100.0, 105.0, [], {}, i < 3)
            metrics.instance_metrics.append(instance)
        
        summary = metrics.to_summary_dict()
        
        assert summary['run_id'] == "test_run"
        assert summary['duration'] == 50.0
        assert summary['total_instances'] == 5
        assert summary['successful_instances'] == 3
        assert summary['failed_instances'] == 2
        assert summary['success_rate'] == 60.0
