"""
Circuit-to-CNF encoding via Tseitin transformation.

The Tseitin transformation converts a circuit into equisatisfiable CNF by:
1. Introducing a variable for each gate
2. Adding clauses that encode each gate's behavior
3. Adding a unit clause asserting the output is true

For a gate g = AND(a, b):
  - (NOT g OR a) AND (NOT g OR b) AND (NOT a OR NOT b OR g)

For a gate g = OR(a, b):
  - (g OR NOT a) AND (g OR NOT b) AND (a OR b OR NOT g)

For a gate g = NOT(a):
  - (NOT g OR NOT a) AND (g OR a)
"""

from pathlib import Path
from typing import Dict, List, Tuple
import sys

# Add parent to path for imports
parent_dir = Path(__file__).parent.parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from search.circuits.dsl import Circuit, Gate, GateType
from search.io.cnf_reader import CNFProblem
from search.io.cnf_writer import CNFWriter


class CircuitEncoder:
    """
    Encodes circuits to CNF using Tseitin transformation.
    
    Each gate in the circuit gets a unique CNF variable.
    Input gates map to their corresponding input variables.
    """
    
    def __init__(self):
        """Initialize encoder."""
        print(f"[CircuitEncoder] Initialized")
        self.gate_to_var: Dict[int, int] = {}  # Maps gate_id to CNF variable
        self.next_var: int = 1
    
    def encode(self, circuit: Circuit) -> CNFProblem:
        """
        Encode circuit to CNF via Tseitin transformation.
        
        Args:
            circuit: Circuit to encode
            
        Returns:
            CNFProblem representing the circuit
            
        Raises:
            ValueError: If circuit is invalid
        """
        print(f"[CircuitEncoder] Encoding circuit with {len(circuit.gates)} gates")
        
        # Validate circuit
        if not circuit.validate_topology():
            raise ValueError("Circuit topology validation failed")
        
        if circuit.output_gate is None:
            raise ValueError("Circuit has no output gate")
        
        # Reset state
        self.gate_to_var = {}
        self.next_var = 1
        
        # Assign variables to all gates
        self._assign_variables(circuit)
        
        print(f"[CircuitEncoder] Assigned {self.next_var - 1} CNF variables")
        
        # Generate clauses for each gate
        clauses: List[List[int]] = []
        for gate_id, gate in circuit.gates.items():
            gate_clauses = self._encode_gate(gate)
            clauses.extend(gate_clauses)
            
            if gate_clauses:
                print(f"[CircuitEncoder] Gate {gate_id} ({gate.gate_type.value}): {len(gate_clauses)} clauses")
        
        # Add unit clause asserting output is true
        output_var = self.gate_to_var[circuit.output_gate]
        clauses.append([output_var])
        print(f"[CircuitEncoder] Added output assertion: [{output_var}]")
        
        # Create CNF problem
        num_vars = self.next_var - 1
        num_clauses = len(clauses)
        
        comments = [
            f"Tseitin encoding of circuit with {len(circuit.gates)} gates",
            f"Circuit size: {circuit.compute_size()}",
            f"Circuit depth: {circuit.compute_depth()}",
            f"Output gate: {circuit.output_gate} -> variable {output_var}",
        ]
        
        cnf = CNFProblem(
            num_vars=num_vars,
            num_clauses=num_clauses,
            clauses=clauses,
            comments=comments,
        )
        
        print(f"[CircuitEncoder] Generated CNF: {num_vars} vars, {num_clauses} clauses")
        return cnf
    
    def _assign_variables(self, circuit: Circuit) -> None:
        """
        Assign CNF variables to gates.
        
        Input gates get variables corresponding to their input index.
        Negated inputs get fresh variables (will be encoded with NOT).
        Other gates get fresh variables.
        """
        # First pass: assign positive input gates to match their variable indices
        for gate_id, gate in circuit.gates.items():
            if gate.gate_type == GateType.INPUT and not gate.negated:
                # Positive input gates map to their variable index
                var = gate.variable
                self.gate_to_var[gate_id] = var
                self.next_var = max(self.next_var, var + 1)
                print(f"[CircuitEncoder] Input gate {gate_id} -> variable {var}")
        
        # Second pass: assign remaining gates (including negated inputs)
        for gate_id, gate in circuit.gates.items():
            if gate_id not in self.gate_to_var:
                var = self.next_var
                self.next_var += 1
                self.gate_to_var[gate_id] = var
                if gate.gate_type == GateType.INPUT and gate.negated:
                    print(f"[CircuitEncoder] Negated input gate {gate_id} (x{gate.variable}) -> variable {var}")
                else:
                    print(f"[CircuitEncoder] Gate {gate_id} ({gate.gate_type.value}) -> variable {var}")
    
    def _encode_gate(self, gate: Gate) -> List[List[int]]:
        """
        Generate clauses encoding a single gate.
        
        Args:
            gate: Gate to encode
            
        Returns:
            List of clauses (each clause is list of literals)
        """
        gate_var = self.gate_to_var[gate.gate_id]
        
        # Input gates: handle negation
        if gate.gate_type == GateType.INPUT:
            if gate.negated:
                # Negated input: encode as NOT of the original variable
                # gate_var = NOT(original_var)
                original_var = gate.variable
                return self._encode_not(gate_var, original_var)
            else:
                # Positive input, no clauses needed
                return []
        
        # Constant gates
        if gate.gate_type == GateType.CONSTANT:
            if gate.value:
                # Gate is always true: add unit clause [gate_var]
                return [[gate_var]]
            else:
                # Gate is always false: add unit clause [-gate_var]
                return [[-gate_var]]
        
        # Get input variables
        input_vars = [self.gate_to_var[inp] for inp in gate.inputs]
        
        # AND gate encoding
        if gate.gate_type == GateType.AND:
            return self._encode_and(gate_var, input_vars)
        
        # OR gate encoding
        if gate.gate_type == GateType.OR:
            return self._encode_or(gate_var, input_vars)
        
        # NOT gate encoding
        if gate.gate_type == GateType.NOT:
            return self._encode_not(gate_var, input_vars[0])
        
        raise ValueError(f"Unknown gate type: {gate.gate_type}")
    
    def _encode_and(self, output: int, inputs: List[int]) -> List[List[int]]:
        """
        Encode AND gate: output = AND(inputs)
        
        Clauses:
          - For each input i: (NOT output OR input_i)
          - (NOT input_1 OR NOT input_2 OR ... OR output)
        
        Args:
            output: Output variable
            inputs: Input variables
            
        Returns:
            List of clauses
        """
        clauses = []
        
        # If output is true, all inputs must be true
        for inp in inputs:
            clauses.append([-output, inp])
        
        # If all inputs are true, output must be true
        clause = [-inp for inp in inputs] + [output]
        clauses.append(clause)
        
        return clauses
    
    def _encode_or(self, output: int, inputs: List[int]) -> List[List[int]]:
        """
        Encode OR gate: output = OR(inputs)
        
        Clauses:
          - For each input i: (output OR NOT input_i)
          - (input_1 OR input_2 OR ... OR NOT output)
        
        Args:
            output: Output variable
            inputs: Input variables
            
        Returns:
            List of clauses
        """
        clauses = []
        
        # If any input is true, output must be true
        clause = inputs + [-output]
        clauses.append(clause)
        
        # If output is true, at least one input is true (implied by above)
        # But we also need: if output is false, all inputs are false
        for inp in inputs:
            clauses.append([output, -inp])
        
        return clauses
    
    def _encode_not(self, output: int, input_var: int) -> List[List[int]]:
        """
        Encode NOT gate: output = NOT(input)
        
        Clauses:
          - (NOT output OR NOT input)
          - (output OR input)
        
        Args:
            output: Output variable
            input_var: Input variable
            
        Returns:
            List of clauses
        """
        return [
            [-output, -input_var],  # output => NOT input
            [output, input_var],     # NOT output => input
        ]
    
    def get_variable_mapping(self) -> Dict[int, int]:
        """
        Get mapping from gate IDs to CNF variables.
        
        Returns:
            Dictionary mapping gate_id to CNF variable
        """
        return self.gate_to_var.copy()
    
    def write_to_file(self, circuit: Circuit, file_path: Path) -> CNFProblem:
        """
        Convenience method: encode circuit and write to file.
        
        Args:
            circuit: Circuit to encode
            file_path: Output CNF file path
            
        Returns:
            CNFProblem that was written
        """
        print(f"[CircuitEncoder] Writing circuit to {file_path}")
        
        cnf = self.encode(circuit)
        
        writer = CNFWriter()
        writer.write(cnf, file_path)
        
        print(f"[CircuitEncoder] Successfully wrote CNF to {file_path}")
        return cnf


def encode_circuit(circuit: Circuit) -> CNFProblem:
    """
    Convenience function to encode a circuit to CNF.
    
    Args:
        circuit: Circuit to encode
        
    Returns:
        CNFProblem representing the circuit
    """
    encoder = CircuitEncoder()
    return encoder.encode(circuit)


def encode_and_write(circuit: Circuit, file_path: Path) -> CNFProblem:
    """
    Convenience function to encode circuit and write to file.
    
    Args:
        circuit: Circuit to encode
        file_path: Output file path
        
    Returns:
        CNFProblem that was written
    """
    encoder = CircuitEncoder()
    return encoder.write_to_file(circuit, file_path)

