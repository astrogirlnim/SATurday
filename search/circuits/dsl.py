"""
Circuit DSL - Domain-specific language for circuit construction.

Provides constructors for:
- Monotone circuits (no NOT gates except on inputs)
- AC0 circuits (constant depth, unbounded fan-in AND/OR/NOT)
- Formula circuits (fan-out 1, tree structure)

Each circuit can compute size, depth, and validate constraints.
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import List, Set, Optional, Dict


class GateType(Enum):
    """Circuit gate types."""
    INPUT = "INPUT"      # Input variable or its negation
    AND = "AND"          # Conjunction
    OR = "OR"            # Disjunction
    NOT = "NOT"          # Negation
    CONSTANT = "CONSTANT"  # True/False constants


@dataclass
class Gate:
    """
    Represents a single gate in a circuit.
    
    Attributes:
        gate_id: Unique identifier for this gate
        gate_type: Type of gate (INPUT, AND, OR, NOT, CONSTANT)
        inputs: List of gate IDs that feed into this gate
        label: Optional human-readable label
        value: For CONSTANT gates, the boolean value; for INPUT, the variable index
    """
    gate_id: int
    gate_type: GateType
    inputs: List[int] = field(default_factory=list)
    label: Optional[str] = None
    value: Optional[bool] = None  # For constants
    variable: Optional[int] = None  # For input gates (1-indexed)
    negated: bool = False  # For negated inputs
    
    def __str__(self) -> str:
        """String representation for debugging."""
        if self.gate_type == GateType.INPUT:
            var_str = f"{'~' if self.negated else ''}x{self.variable}"
            return f"Gate{self.gate_id}[INPUT: {var_str}]"
        elif self.gate_type == GateType.CONSTANT:
            return f"Gate{self.gate_id}[CONST: {self.value}]"
        else:
            input_str = ','.join(str(i) for i in self.inputs)
            return f"Gate{self.gate_id}[{self.gate_type.value}: ({input_str})]"


class Circuit:
    """
    Base circuit class with gates and topology.
    
    Circuits are built from gates with a designated output gate.
    Gates are stored in a dictionary keyed by gate_id.
    """
    
    def __init__(self, num_inputs: int):
        """
        Initialize circuit.
        
        Args:
            num_inputs: Number of input variables
        """
        self.num_inputs = num_inputs
        self.gates: Dict[int, Gate] = {}
        self.output_gate: Optional[int] = None
        self.next_gate_id = 0
        
        print(f"[Circuit] Initialized with {num_inputs} inputs")
    
    def add_input(self, variable: int, negated: bool = False) -> int:
        """
        Add input gate for a variable.
        
        Args:
            variable: Variable index (1-indexed)
            negated: Whether this is a negated input
            
        Returns:
            Gate ID
        """
        gate_id = self.next_gate_id
        self.next_gate_id += 1
        
        gate = Gate(
            gate_id=gate_id,
            gate_type=GateType.INPUT,
            variable=variable,
            negated=negated,
        )
        self.gates[gate_id] = gate
        
        print(f"[Circuit] Added input gate {gate_id}: {'~' if negated else ''}x{variable}")
        return gate_id
    
    def add_constant(self, value: bool) -> int:
        """Add constant gate (True or False)."""
        gate_id = self.next_gate_id
        self.next_gate_id += 1
        
        gate = Gate(
            gate_id=gate_id,
            gate_type=GateType.CONSTANT,
            value=value,
        )
        self.gates[gate_id] = gate
        
        print(f"[Circuit] Added constant gate {gate_id}: {value}")
        return gate_id
    
    def add_and(self, input_gates: List[int], label: Optional[str] = None) -> int:
        """
        Add AND gate.
        
        Args:
            input_gates: List of gate IDs to AND together
            label: Optional label for debugging
            
        Returns:
            Gate ID
        """
        gate_id = self.next_gate_id
        self.next_gate_id += 1
        
        gate = Gate(
            gate_id=gate_id,
            gate_type=GateType.AND,
            inputs=input_gates,
            label=label,
        )
        self.gates[gate_id] = gate
        
        print(f"[Circuit] Added AND gate {gate_id} with {len(input_gates)} inputs")
        return gate_id
    
    def add_or(self, input_gates: List[int], label: Optional[str] = None) -> int:
        """
        Add OR gate.
        
        Args:
            input_gates: List of gate IDs to OR together
            label: Optional label for debugging
            
        Returns:
            Gate ID
        """
        gate_id = self.next_gate_id
        self.next_gate_id += 1
        
        gate = Gate(
            gate_id=gate_id,
            gate_type=GateType.OR,
            inputs=input_gates,
            label=label,
        )
        self.gates[gate_id] = gate
        
        print(f"[Circuit] Added OR gate {gate_id} with {len(input_gates)} inputs")
        return gate_id
    
    def add_not(self, input_gate: int, label: Optional[str] = None) -> int:
        """
        Add NOT gate.
        
        Args:
            input_gate: Gate ID to negate
            label: Optional label
            
        Returns:
            Gate ID
        """
        gate_id = self.next_gate_id
        self.next_gate_id += 1
        
        gate = Gate(
            gate_id=gate_id,
            gate_type=GateType.NOT,
            inputs=[input_gate],
            label=label,
        )
        self.gates[gate_id] = gate
        
        print(f"[Circuit] Added NOT gate {gate_id}")
        return gate_id
    
    def set_output(self, gate_id: int) -> None:
        """Set the output gate of the circuit."""
        if gate_id not in self.gates:
            raise ValueError(f"Gate {gate_id} does not exist")
        
        self.output_gate = gate_id
        print(f"[Circuit] Set output to gate {gate_id}")
    
    def compute_size(self) -> int:
        """
        Compute circuit size (number of gates excluding inputs).
        
        Returns:
            Number of non-input gates
        """
        size = sum(
            1 for gate in self.gates.values()
            if gate.gate_type not in [GateType.INPUT, GateType.CONSTANT]
        )
        print(f"[Circuit] Computed size: {size} gates")
        return size
    
    def compute_depth(self) -> int:
        """
        Compute circuit depth (longest path from input to output).
        
        Returns:
            Maximum depth
        """
        if self.output_gate is None:
            return 0
        
        # Memoization for depth computation
        depths: Dict[int, int] = {}
        
        def gate_depth(gate_id: int) -> int:
            if gate_id in depths:
                return depths[gate_id]
            
            gate = self.gates[gate_id]
            
            # Base cases
            if gate.gate_type in [GateType.INPUT, GateType.CONSTANT]:
                depths[gate_id] = 0
                return 0
            
            # Recursive case: 1 + max depth of inputs
            if not gate.inputs:
                depths[gate_id] = 0
                return 0
            
            max_input_depth = max(gate_depth(inp) for inp in gate.inputs)
            depths[gate_id] = 1 + max_input_depth
            return depths[gate_id]
        
        depth = gate_depth(self.output_gate)
        print(f"[Circuit] Computed depth: {depth}")
        return depth
    
    def get_gate_count_by_type(self) -> Dict[GateType, int]:
        """Get count of gates by type."""
        counts: Dict[GateType, int] = {gt: 0 for gt in GateType}
        for gate in self.gates.values():
            counts[gate.gate_type] += 1
        return counts
    
    def validate_topology(self) -> bool:
        """
        Validate circuit topology (no cycles, inputs valid, etc.).
        
        Returns:
            True if valid, False otherwise
        """
        print(f"[Circuit] Validating topology...")
        
        # Check output gate exists
        if self.output_gate is None:
            print(f"[Circuit] ERROR: No output gate set")
            return False
        
        # Check all gate inputs reference existing gates
        for gate_id, gate in self.gates.items():
            for inp in gate.inputs:
                if inp not in self.gates:
                    print(f"[Circuit] ERROR: Gate {gate_id} references non-existent gate {inp}")
                    return False
        
        # Check for cycles using DFS
        visited: Set[int] = set()
        rec_stack: Set[int] = set()
        
        def has_cycle(gate_id: int) -> bool:
            visited.add(gate_id)
            rec_stack.add(gate_id)
            
            gate = self.gates[gate_id]
            for inp in gate.inputs:
                if inp not in visited:
                    if has_cycle(inp):
                        return True
                elif inp in rec_stack:
                    print(f"[Circuit] ERROR: Cycle detected at gate {inp}")
                    return True
            
            rec_stack.remove(gate_id)
            return False
        
        if has_cycle(self.output_gate):
            return False
        
        print(f"[Circuit] Topology validation passed")
        return True


class MonotoneCircuit(Circuit):
    """
    Monotone circuit - only AND and OR gates (no NOT except on inputs).
    
    Monotone circuits compute monotone Boolean functions where
    flipping any input from 0 to 1 cannot change the output from 1 to 0.
    """
    
    def add_not(self, input_gate: int, label: Optional[str] = None) -> int:
        """
        Override: NOT gates not allowed except on inputs.
        
        Raises:
            ValueError: Always (NOT not allowed in monotone circuits)
        """
        raise ValueError("NOT gates not allowed in monotone circuits (except negated inputs)")
    
    def validate(self) -> bool:
        """
        Validate monotone circuit constraints.
        
        Returns:
            True if circuit is valid monotone circuit
        """
        print(f"[MonotoneCircuit] Validating monotone constraints...")
        
        # Check topology first
        if not self.validate_topology():
            return False
        
        # Check no NOT gates (except inputs can be negated)
        for gate in self.gates.values():
            if gate.gate_type == GateType.NOT:
                print(f"[MonotoneCircuit] ERROR: Found NOT gate {gate.gate_id}")
                return False
        
        print(f"[MonotoneCircuit] Validation passed")
        return True


class AC0Circuit(Circuit):
    """
    AC0 circuit - constant depth, unbounded fan-in AND/OR/NOT gates.
    
    AC0 is the class of functions computable by polynomial-size,
    constant-depth circuits with unbounded fan-in AND/OR/NOT gates.
    """
    
    def __init__(self, num_inputs: int, max_depth: int):
        """
        Initialize AC0 circuit.
        
        Args:
            num_inputs: Number of input variables
            max_depth: Maximum allowed depth
        """
        super().__init__(num_inputs)
        self.max_depth = max_depth
        print(f"[AC0Circuit] Max depth: {max_depth}")
    
    def validate(self) -> bool:
        """
        Validate AC0 circuit constraints.
        
        Returns:
            True if circuit satisfies AC0 constraints
        """
        print(f"[AC0Circuit] Validating AC0 constraints...")
        
        # Check topology first
        if not self.validate_topology():
            return False
        
        # Check depth constraint
        depth = self.compute_depth()
        if depth > self.max_depth:
            print(f"[AC0Circuit] ERROR: Depth {depth} exceeds max {self.max_depth}")
            return False
        
        print(f"[AC0Circuit] Validation passed (depth={depth}/{self.max_depth})")
        return True


class FormulaCircuit(Circuit):
    """
    Formula circuit - fan-out 1 (tree structure).
    
    Each gate (except output) feeds into exactly one other gate.
    Forms a tree rather than a DAG.
    """
    
    def validate(self) -> bool:
        """
        Validate formula circuit constraints (fan-out 1).
        
        Returns:
            True if circuit is a valid formula
        """
        print(f"[FormulaCircuit] Validating formula constraints...")
        
        # Check topology first
        if not self.validate_topology():
            return False
        
        # Check fan-out: each gate (except output) used at most once
        fanout: Dict[int, int] = {gate_id: 0 for gate_id in self.gates}
        
        for gate in self.gates.values():
            for inp in gate.inputs:
                fanout[inp] += 1
        
        # All gates except output should have fan-out exactly 1
        for gate_id, fo in fanout.items():
            if gate_id == self.output_gate:
                continue  # Output can have fan-out 0
            
            gate = self.gates[gate_id]
            if gate.gate_type in [GateType.INPUT, GateType.CONSTANT]:
                # Inputs can have any fan-out in formulas
                continue
            
            if fo != 1:
                print(f"[FormulaCircuit] ERROR: Gate {gate_id} has fan-out {fo}, expected 1")
                return False
        
        print(f"[FormulaCircuit] Validation passed (tree structure)")
        return True


# Utility functions for common circuit patterns

def build_and_tree(circuit: Circuit, input_gates: List[int]) -> int:
    """
    Build balanced AND tree over inputs.
    
    Args:
        circuit: Circuit to add gates to
        input_gates: List of gate IDs to AND together
        
    Returns:
        Gate ID of root AND gate
    """
    if len(input_gates) == 0:
        raise ValueError("Cannot build AND tree with no inputs")
    if len(input_gates) == 1:
        return input_gates[0]
    
    print(f"[build_and_tree] Building AND tree for {len(input_gates)} inputs")
    
    # Build balanced binary tree
    current_level = input_gates
    while len(current_level) > 1:
        next_level = []
        for i in range(0, len(current_level), 2):
            if i + 1 < len(current_level):
                # Pair available
                and_gate = circuit.add_and([current_level[i], current_level[i+1]])
                next_level.append(and_gate)
            else:
                # Odd one out
                next_level.append(current_level[i])
        current_level = next_level
    
    return current_level[0]


def build_or_tree(circuit: Circuit, input_gates: List[int]) -> int:
    """
    Build balanced OR tree over inputs.
    
    Args:
        circuit: Circuit to add gates to
        input_gates: List of gate IDs to OR together
        
    Returns:
        Gate ID of root OR gate
    """
    if len(input_gates) == 0:
        raise ValueError("Cannot build OR tree with no inputs")
    if len(input_gates) == 1:
        return input_gates[0]
    
    print(f"[build_or_tree] Building OR tree for {len(input_gates)} inputs")
    
    current_level = input_gates
    while len(current_level) > 1:
        next_level = []
        for i in range(0, len(current_level), 2):
            if i + 1 < len(current_level):
                or_gate = circuit.add_or([current_level[i], current_level[i+1]])
                next_level.append(or_gate)
            else:
                next_level.append(current_level[i])
        current_level = next_level
    
    return current_level[0]

