"""
Template system for conjecture generation.

This module provides template-based generation of:
- Lean theorem stubs with sorry placeholders
- CNF specifications for SAT mining

Templates are bet-specific and parameterized by task details.
"""

from .base import ConjectureTemplate, Conjecture
from .bet_a_circuits import (
    MonotoneParityTemplate,
    MonotoneMajorityTemplate,
    AC0ParityTemplate,
    AC0MajorityTemplate,
    FormulaParityTemplate,
)

__all__ = [
    "ConjectureTemplate",
    "Conjecture",
    "MonotoneParityTemplate",
    "MonotoneMajorityTemplate",
    "AC0ParityTemplate",
    "AC0MajorityTemplate",
    "FormulaParityTemplate",
]
