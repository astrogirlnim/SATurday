"""
Core agent interface and base classes for SATurday agent system.

This module defines the AgentBase abstract class that all agents must implement.
Agents follow a three-phase lifecycle: plan, act, report.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional
import time
import json


@dataclass
class AgentContext:
    """
    Context passed to agents during execution.
    
    Contains shared state, configuration, and artifacts from previous agents.
    """
    
    # Execution metadata
    run_id: str
    seed: int
    timestamp: str
    
    # Shared configuration
    config: Dict[str, Any] = field(default_factory=dict)
    
    # Artifacts from previous agents
    artifacts: Dict[str, Any] = field(default_factory=dict)
    
    # Logging callback
    log_callback: Optional[Any] = None
    
    def log(self, agent_name: str, message: str, level: str = "INFO") -> None:
        """Log a message from an agent."""
        log_entry = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "run_id": self.run_id,
            "agent": agent_name,
            "level": level,
            "message": message,
        }
        
        if self.log_callback:
            self.log_callback(log_entry)
        else:
            # Fallback to print
            print(f"[{log_entry['timestamp']}] [{agent_name}] {level}: {message}")


@dataclass
class AgentResult:
    """
    Result returned by an agent after execution.
    
    Contains status, artifacts produced, and optional error information.
    """
    
    agent_name: str
    status: str  # "success", "failure", "skipped"
    artifacts: Dict[str, Any] = field(default_factory=dict)
    metrics: Dict[str, Any] = field(default_factory=dict)
    error: Optional[str] = None
    duration_seconds: float = 0.0
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert result to dictionary for JSON serialization."""
        return {
            "agent_name": self.agent_name,
            "status": self.status,
            "artifacts": self.artifacts,
            "metrics": self.metrics,
            "error": self.error,
            "duration_seconds": self.duration_seconds,
        }


class AgentBase(ABC):
    """
    Abstract base class for all SATurday agents.
    
    All agents must implement three methods:
    - plan(): Decompose work into subtasks
    - act(): Execute primary logic
    - report(): Generate outputs
    
    Agents receive context and return results.
    """
    
    def __init__(self, name: str):
        """
        Initialize agent with a name.
        
        Args:
            name: Unique identifier for this agent
        """
        self.name = name
    
    @abstractmethod
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Plan phase: Decompose work into subtasks.
        
        Args:
            context: Execution context with config and artifacts
        
        Returns:
            Dictionary with plan details (tasks, dependencies, etc.)
        """
        pass
    
    @abstractmethod
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Act phase: Execute primary agent logic.
        
        Args:
            context: Execution context
            plan: Plan from plan() phase
        
        Returns:
            AgentResult with status and artifacts
        """
        pass
    
    @abstractmethod
    def report(self, context: AgentContext, result: AgentResult) -> str:
        """
        Report phase: Generate human-readable report.
        
        Args:
            context: Execution context
            result: Result from act() phase
        
        Returns:
            Markdown-formatted report string
        """
        pass
    
    def execute(self, context: AgentContext) -> AgentResult:
        """
        Execute full agent lifecycle: plan -> act -> report.
        
        This is the main entry point called by the supervisor.
        
        Args:
            context: Execution context
        
        Returns:
            AgentResult with execution status
        """
        context.log(self.name, f"Starting execution")
        start_time = time.time()
        
        try:
            # Phase 1: Plan
            context.log(self.name, "Phase 1: Planning")
            plan = self.plan(context)
            context.log(self.name, f"Plan: {json.dumps(plan, indent=2)}")
            
            # Phase 2: Act
            context.log(self.name, "Phase 2: Acting")
            result = self.act(context, plan)
            
            # Phase 3: Report
            context.log(self.name, "Phase 3: Reporting")
            report = self.report(context, result)
            result.artifacts["report"] = report
            
            # Record duration
            result.duration_seconds = time.time() - start_time
            
            context.log(
                self.name,
                f"Completed in {result.duration_seconds:.3f}s with status: {result.status}"
            )
            
            return result
        
        except Exception as e:
            # Handle errors gracefully
            duration = time.time() - start_time
            context.log(self.name, f"ERROR: {str(e)}", level="ERROR")
            
            return AgentResult(
                agent_name=self.name,
                status="failure",
                error=str(e),
                duration_seconds=duration,
            )

