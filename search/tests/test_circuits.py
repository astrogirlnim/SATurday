"""
Unit tests for circuit DSL and CNF encoding.

Tests:
- Circuit construction (monotone, AC0, formula)
- Gate operations
- Size and depth computation
- Validation constraints
- Tseitin encoding
- Integration with Kissat
"""

import pytest
from pathlib import Path
import tempfile
import shutil
import subprocess
import json

# Add parent to path
import sys
parent_dir = Path(__file__).parent.parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from search.circuits.dsl import (
    Circuit,
    MonotoneCircuit,
    AC0Circuit,
    FormulaCircuit,
    GateType,
    build_and_tree,
    build_or_tree,
)
from search.circuits.to_cnf import CircuitEncoder, encode_circuit


class TestCircuitConstruction:
    """Test basic circuit construction."""
    
    def test_create_empty_circuit(self):
        """Test creating an empty circuit."""
        print("\n[TEST] test_create_empty_circuit")
        circuit = Circuit(num_inputs=3)
        assert circuit.num_inputs == 3
        assert len(circuit.gates) == 0
        print("[TEST] PASS")
    
    def test_add_input_gates(self):
        """Test adding input gates."""
        print("\n[TEST] test_add_input_gates")
        circuit = Circuit(num_inputs=2)
        
        g1 = circuit.add_input(1, negated=False)
        g2 = circuit.add_input(2, negated=True)
        
        assert circuit.gates[g1].gate_type == GateType.INPUT
        assert circuit.gates[g1].variable == 1
        assert not circuit.gates[g1].negated
        
        assert circuit.gates[g2].gate_type == GateType.INPUT
        assert circuit.gates[g2].variable == 2
        assert circuit.gates[g2].negated
        
        print("[TEST] PASS")
    
    def test_add_and_gate(self):
        """Test adding AND gate."""
        print("\n[TEST] test_add_and_gate")
        circuit = Circuit(num_inputs=2)
        
        g1 = circuit.add_input(1)
        g2 = circuit.add_input(2)
        g_and = circuit.add_and([g1, g2])
        
        assert circuit.gates[g_and].gate_type == GateType.AND
        assert circuit.gates[g_and].inputs == [g1, g2]
        
        print("[TEST] PASS")
    
    def test_add_or_gate(self):
        """Test adding OR gate."""
        print("\n[TEST] test_add_or_gate")
        circuit = Circuit(num_inputs=2)
        
        g1 = circuit.add_input(1)
        g2 = circuit.add_input(2)
        g_or = circuit.add_or([g1, g2])
        
        assert circuit.gates[g_or].gate_type == GateType.OR
        assert circuit.gates[g_or].inputs == [g1, g2]
        
        print("[TEST] PASS")
    
    def test_simple_circuit_with_output(self):
        """Test circuit with output gate set."""
        print("\n[TEST] test_simple_circuit_with_output")
        circuit = Circuit(num_inputs=2)
        
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        out = circuit.add_and([x1, x2])
        circuit.set_output(out)
        
        assert circuit.output_gate == out
        assert circuit.validate_topology()
        
        print("[TEST] PASS")


class TestCircuitMetrics:
    """Test circuit size and depth computation."""
    
    def test_simple_circuit_size(self):
        """Test size computation for simple circuit."""
        print("\n[TEST] test_simple_circuit_size")
        circuit = Circuit(num_inputs=2)
        
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        g = circuit.add_and([x1, x2])
        circuit.set_output(g)
        
        size = circuit.compute_size()
        assert size == 1  # Only the AND gate
        print("[TEST] PASS")
    
    def test_layered_circuit_depth(self):
        """Test depth computation for layered circuit."""
        print("\n[TEST] test_layered_circuit_depth")
        circuit = Circuit(num_inputs=4)
        
        # Layer 0: inputs
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        x3 = circuit.add_input(3)
        x4 = circuit.add_input(4)
        
        # Layer 1: AND gates
        g1 = circuit.add_and([x1, x2])
        g2 = circuit.add_and([x3, x4])
        
        # Layer 2: OR gate
        out = circuit.add_or([g1, g2])
        circuit.set_output(out)
        
        depth = circuit.compute_depth()
        assert depth == 2
        
        size = circuit.compute_size()
        assert size == 3  # 2 AND + 1 OR
        
        print("[TEST] PASS")


class TestMonotoneCircuit:
    """Test monotone circuit constraints."""
    
    def test_monotone_allows_and_or(self):
        """Test monotone circuit with AND/OR."""
        print("\n[TEST] test_monotone_allows_and_or")
        circuit = MonotoneCircuit(num_inputs=3)
        
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        x3 = circuit.add_input(3)
        
        g1 = circuit.add_and([x1, x2])
        g2 = circuit.add_or([g1, x3])
        circuit.set_output(g2)
        
        assert circuit.validate()
        print("[TEST] PASS")
    
    def test_monotone_rejects_not(self):
        """Test monotone circuit rejects NOT gates."""
        print("\n[TEST] test_monotone_rejects_not")
        circuit = MonotoneCircuit(num_inputs=2)
        
        x1 = circuit.add_input(1)
        
        # Should raise ValueError
        with pytest.raises(ValueError, match="NOT gates not allowed"):
            circuit.add_not(x1)
        
        print("[TEST] PASS")
    
    def test_monotone_allows_negated_inputs(self):
        """Test monotone allows negated inputs."""
        print("\n[TEST] test_monotone_allows_negated_inputs")
        circuit = MonotoneCircuit(num_inputs=2)
        
        x1 = circuit.add_input(1, negated=False)
        x2 = circuit.add_input(2, negated=True)  # Negated input OK
        
        out = circuit.add_and([x1, x2])
        circuit.set_output(out)
        
        assert circuit.validate()
        print("[TEST] PASS")


class TestAC0Circuit:
    """Test AC0 circuit constraints."""
    
    def test_ac0_depth_constraint(self):
        """Test AC0 enforces depth limit."""
        print("\n[TEST] test_ac0_depth_constraint")
        circuit = AC0Circuit(num_inputs=4, max_depth=2)
        
        # Build circuit with depth 2
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        x3 = circuit.add_input(3)
        x4 = circuit.add_input(4)
        
        g1 = circuit.add_and([x1, x2])  # Depth 1
        g2 = circuit.add_or([g1, x3, x4])  # Depth 2
        circuit.set_output(g2)
        
        assert circuit.validate()
        print("[TEST] PASS")
    
    def test_ac0_unbounded_fanin(self):
        """Test AC0 allows unbounded fan-in."""
        print("\n[TEST] test_ac0_unbounded_fanin")
        circuit = AC0Circuit(num_inputs=10, max_depth=1)
        
        # Build OR gate with 10 inputs (unbounded fan-in)
        inputs = [circuit.add_input(i+1) for i in range(10)]
        out = circuit.add_or(inputs)
        circuit.set_output(out)
        
        assert circuit.compute_depth() == 1
        assert circuit.validate()
        print("[TEST] PASS")


class TestFormulaCircuit:
    """Test formula circuit constraints."""
    
    def test_formula_tree_structure(self):
        """Test formula circuit validates tree structure."""
        print("\n[TEST] test_formula_tree_structure")
        circuit = FormulaCircuit(num_inputs=4)
        
        # Build tree: ((x1 AND x2) OR (x3 AND x4))
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        x3 = circuit.add_input(3)
        x4 = circuit.add_input(4)
        
        g1 = circuit.add_and([x1, x2])  # Used once
        g2 = circuit.add_and([x3, x4])  # Used once
        out = circuit.add_or([g1, g2])
        circuit.set_output(out)
        
        assert circuit.validate()
        print("[TEST] PASS")


class TestCircuitHelpers:
    """Test helper functions."""
    
    def test_build_and_tree(self):
        """Test AND tree builder."""
        print("\n[TEST] test_build_and_tree")
        circuit = Circuit(num_inputs=4)
        
        inputs = [circuit.add_input(i+1) for i in range(4)]
        root = build_and_tree(circuit, inputs)
        circuit.set_output(root)
        
        # Tree of 4 inputs should have depth 2
        assert circuit.compute_depth() == 2
        print("[TEST] PASS")
    
    def test_build_or_tree(self):
        """Test OR tree builder."""
        print("\n[TEST] test_build_or_tree")
        circuit = Circuit(num_inputs=4)
        
        inputs = [circuit.add_input(i+1) for i in range(4)]
        root = build_or_tree(circuit, inputs)
        circuit.set_output(root)
        
        assert circuit.compute_depth() == 2
        print("[TEST] PASS")


class TestTseitinEncoding:
    """Test Tseitin CNF encoding."""
    
    def test_encode_simple_and(self):
        """Test encoding simple AND circuit."""
        print("\n[TEST] test_encode_simple_and")
        circuit = Circuit(num_inputs=2)
        
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        out = circuit.add_and([x1, x2])
        circuit.set_output(out)
        
        encoder = CircuitEncoder()
        cnf = encoder.encode(circuit)
        
        # Should have clauses encoding the AND gate
        assert cnf.num_vars >= 2
        assert cnf.num_clauses > 0
        assert cnf.validate()[0]
        
        print(f"[TEST] Generated {cnf.num_clauses} clauses")
        print("[TEST] PASS")
    
    def test_encode_simple_or(self):
        """Test encoding simple OR circuit."""
        print("\n[TEST] test_encode_simple_or")
        circuit = Circuit(num_inputs=2)
        
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        out = circuit.add_or([x1, x2])
        circuit.set_output(out)
        
        encoder = CircuitEncoder()
        cnf = encoder.encode(circuit)
        
        assert cnf.num_vars >= 2
        assert cnf.num_clauses > 0
        assert cnf.validate()[0]
        
        print("[TEST] PASS")
    
    def test_encode_layered_circuit(self):
        """Test encoding layered circuit."""
        print("\n[TEST] test_encode_layered_circuit")
        circuit = Circuit(num_inputs=4)
        
        # ((x1 AND x2) OR (x3 AND x4))
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        x3 = circuit.add_input(3)
        x4 = circuit.add_input(4)
        
        g1 = circuit.add_and([x1, x2])
        g2 = circuit.add_and([x3, x4])
        out = circuit.add_or([g1, g2])
        circuit.set_output(out)
        
        cnf = encode_circuit(circuit)
        
        print(f"[TEST] Circuit: size={circuit.compute_size()}, depth={circuit.compute_depth()}")
        print(f"[TEST] CNF: {cnf.num_vars} vars, {cnf.num_clauses} clauses")
        assert cnf.validate()[0]
        
        print("[TEST] PASS")


class TestKissatIntegration:
    """Test CNF generation and solving with Kissat."""
    
    @pytest.fixture
    def temp_dir(self):
        """Create temporary directory."""
        temp = Path(tempfile.mkdtemp())
        yield temp
        shutil.rmtree(temp)
    
    def test_sat_circuit_with_kissat(self, temp_dir: Path):
        """Test generating SAT circuit and solving with Kissat."""
        print("\n[TEST] test_sat_circuit_with_kissat")
        
        # Build trivial SAT circuit: x1 OR x2
        circuit = Circuit(num_inputs=2)
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        out = circuit.add_or([x1, x2])
        circuit.set_output(out)
        
        # Encode to CNF
        encoder = CircuitEncoder()
        cnf = encoder.write_to_file(circuit, temp_dir / "sat_circuit.cnf")
        
        print(f"[TEST] Generated CNF with {cnf.num_clauses} clauses")
        
        # Run Kissat (if available)
        kissat_bin = Path(__file__).parent.parent.parent / "infra" / "build" / "kissat"
        if kissat_bin.exists():
            result = subprocess.run(
                [str(kissat_bin), str(temp_dir / "sat_circuit.cnf")],
                capture_output=True,
                text=True,
                timeout=5,
            )
            print(f"[TEST] Kissat exit code: {result.returncode}")
            assert result.returncode == 10  # SAT
            print("[TEST] Kissat confirmed SAT")
        else:
            print("[TEST] Kissat not found, skipping solver test")
        
        print("[TEST] PASS")
    
    def test_unsat_circuit_with_kissat(self, temp_dir: Path):
        """Test generating UNSAT circuit and solving with Kissat."""
        print("\n[TEST] test_unsat_circuit_with_kissat")
        
        # Build UNSAT circuit: (x1) AND (NOT x1)
        circuit = Circuit(num_inputs=1)
        x1_pos = circuit.add_input(1, negated=False)
        x1_neg = circuit.add_input(1, negated=True)
        out = circuit.add_and([x1_pos, x1_neg])
        circuit.set_output(out)
        
        # Encode to CNF
        encoder = CircuitEncoder()
        cnf = encoder.write_to_file(circuit, temp_dir / "unsat_circuit.cnf")
        
        print(f"[TEST] Generated CNF with {cnf.num_clauses} clauses")
        
        # Run Kissat (if available)
        kissat_bin = Path(__file__).parent.parent.parent / "infra" / "build" / "kissat"
        if kissat_bin.exists():
            result = subprocess.run(
                [str(kissat_bin), str(temp_dir / "unsat_circuit.cnf")],
                capture_output=True,
                text=True,
                timeout=5,
            )
            print(f"[TEST] Kissat exit code: {result.returncode}")
            assert result.returncode == 20  # UNSAT
            print("[TEST] Kissat confirmed UNSAT")
        else:
            print("[TEST] Kissat not found, skipping solver test")
        
        print("[TEST] PASS")
    
    def test_monotone_circuit_encoding(self, temp_dir: Path):
        """Test encoding monotone circuit."""
        print("\n[TEST] test_monotone_circuit_encoding")
        
        # Build monotone circuit: (x1 AND x2) OR (x3 AND x4)
        circuit = MonotoneCircuit(num_inputs=4)
        
        x1 = circuit.add_input(1)
        x2 = circuit.add_input(2)
        x3 = circuit.add_input(3)
        x4 = circuit.add_input(4)
        
        g1 = circuit.add_and([x1, x2])
        g2 = circuit.add_and([x3, x4])
        out = circuit.add_or([g1, g2])
        circuit.set_output(out)
        
        assert circuit.validate()
        
        # Encode
        cnf = encode_circuit(circuit)
        print(f"[TEST] Monotone circuit: {cnf.num_vars} vars, {cnf.num_clauses} clauses")
        assert cnf.validate()[0]
        
        print("[TEST] PASS")


if __name__ == "__main__":
    print("=" * 60)
    print("Circuit DSL Test Suite")
    print("=" * 60)
    
    # Run pytest
    pytest.main([__file__, "-v", "--tb=short"])

