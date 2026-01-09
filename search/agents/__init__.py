"""
SATurday Agent System

Multi-agent research loop for P vs NP exploration.
"""

from .core import AgentBase, AgentContext, AgentResult
from .planner import PlannerAgent
from .conjecturer import ConjecturerAgent
from .miner import MinerAgent
from .formalizer import FormalizerAgent
from .critic import CriticAgent
from .supervisor import Supervisor

__all__ = [
    "AgentBase",
    "AgentContext",
    "AgentResult",
    "PlannerAgent",
    "ConjecturerAgent",
    "MinerAgent",
    "FormalizerAgent",
    "CriticAgent",
    "Supervisor",
]

