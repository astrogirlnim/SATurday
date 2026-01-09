"""
Circuit DSL for complexity-theoretic circuit classes.

Supports:
- Monotone circuits (AND/OR only, no NOT gates except on inputs)
- AC0 circuits (constant depth, unbounded fan-in)
- Formula circuits (fan-out 1, tree structure)
- CNF encoding via Tseitin transformation
"""

from .dsl import (
    Gate,
    GateType,
    Circuit,
    MonotoneCircuit,
    AC0Circuit,
    FormulaCircuit,
)
from .to_cnf import CircuitEncoder

__all__ = [
    "Gate",
    "GateType",
    "Circuit",
    "MonotoneCircuit",
    "AC0Circuit",
    "FormulaCircuit",
    "CircuitEncoder",
]

