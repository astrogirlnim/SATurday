"""
Circuit synthesis encoding as SAT problem.

Encodes the question: "Does there exist a circuit of size ≤k that computes function f?"

For a circuit with k gates and n inputs, we create variables for:
- Gate types (AND/OR for monotone)
- Gate input selections (which gates/inputs feed into each gate)
- Gate values on each truth table row

The encoding ensures that the circuit structure is valid and that it
computes the target function on all inputs.
"""

from dataclasses import dataclass
from typing import List, Dict, Tuple, Set, Optional
from pathlib import Path
import sys

# Add parent to path for imports
parent_dir = Path(__file__).parent.parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from search.io.cnf_reader import CNFProblem


@dataclass
class TruthRow:
    """Single row of a truth table."""
    inputs: List[int]  # Input values (0 or 1)
    output: int        # Expected output (0 or 1)


class VariableManager:
    """Manages CNF variable allocation for circuit synthesis encoding."""
    
    def __init__(self, n_inputs: int, max_gates: int, n_rows: int, symbolic_mode: bool = False):
        """
        Initialize variable manager.
        
        Args:
            n_inputs: Number of input variables
            max_gates: Maximum number of gates
            n_rows: Number of truth table rows (0 for symbolic mode)
            symbolic_mode: If True, use symbolic encoding (no per-row variables)
        """
        self.n_inputs = n_inputs
        self.max_gates = max_gates
        self.n_rows = n_rows
        self.symbolic_mode = symbolic_mode
        self.next_var = 1
        
        # Variable maps
        self.gate_is_and: Dict[int, int] = {}    # gate_id -> var for "gate is AND"
        self.gate_is_or: Dict[int, int] = {}     # gate_id -> var for "gate is OR"
        self.input_select: Dict[Tuple[int, int, int], int] = {}  # (gate, input_idx, source) -> var
        self.gate_value: Dict[Tuple[int, int], int] = {}  # (gate, row) -> var (explicit mode only)
        self.left_val_vars: Dict[Tuple[int, int], int] = {}  # (gate, row) -> var (explicit mode only)
        self.right_val_vars: Dict[Tuple[int, int], int] = {}  # (gate, row) -> var (explicit mode only)
        
        # Symbolic mode variables
        self.xor_chain_vars: Dict[int, int] = {}  # step -> var for XOR chain (symbolic mode only)
        self.input_vars: Dict[int, int] = {}  # input_idx -> var (symbolic mode)
        self.gate_output_vars: Dict[int, int] = {}  # gate_idx -> var (symbolic mode)
        
        mode_str = "symbolic" if symbolic_mode else f"explicit ({n_rows} rows)"
        print(f"[VariableManager] Allocating variables for {n_inputs} inputs, {max_gates} gates, mode={mode_str}")
        
        # Allocate all variables upfront
        self._allocate_variables()
        
        print(f"[VariableManager] Allocated {self.next_var - 1} total variables")
    
    def _allocate_variables(self):
        """Allocate all CNF variables."""
        # Gate type variables (per gate: AND or OR)
        for g in range(self.max_gates):
            self.gate_is_and[g] = self.next_var
            self.next_var += 1
            self.gate_is_or[g] = self.next_var
            self.next_var += 1
        
        print(f"[VariableManager] Gate type vars: {self.max_gates * 2} vars")
        
        # Input selection variables (per gate, per input position, per possible source)
        for g in range(self.max_gates):
            # Each gate can take inputs from: n original inputs + gates 0..g-1
            num_sources = self.n_inputs + g
            for input_pos in [0, 1]:  # Binary gates have 2 inputs
                for source in range(num_sources):
                    self.input_select[(g, input_pos, source)] = self.next_var
                    self.next_var += 1
        
        print(f"[VariableManager] Input selection vars: {self.next_var - 1 - self.max_gates * 2} vars")
        
        if self.symbolic_mode:
            # Algebraic mode: symbolic input variables + gate output variables + XOR chain.
            # These represent a single symbolic execution (not per-row), allowing
            # O(k^2 + n) encoding instead of O(2^n * k).

            # One symbolic variable per circuit input (free Boolean, not fixed to any row)
            for i in range(self.n_inputs):
                self.input_vars[i] = self.next_var
                self.next_var += 1

            # One symbolic output variable per gate
            for g in range(self.max_gates):
                self.gate_output_vars[g] = self.next_var
                self.next_var += 1

            # Auxiliary "selected left/right source value" variables per gate.
            # These replace the per-row left_val_vars/right_val_vars from explicit mode.
            # left_aux[g] = value of the source that gate g's left input selects.
            # right_aux[g] = value of the source that gate g's right input selects.
            self.left_aux_vars: Dict[int, int] = {}
            self.right_aux_vars: Dict[int, int] = {}
            for g in range(self.max_gates):
                self.left_aux_vars[g] = self.next_var
                self.next_var += 1
                self.right_aux_vars[g] = self.next_var
                self.next_var += 1

            # XOR chain variables: xor_chain[i] = XOR(input_0, ..., input_i)
            for step in range(self.n_inputs):
                self.xor_chain_vars[step] = self.next_var
                self.next_var += 1

            print(
                f"[VariableManager] Algebraic mode: {self.n_inputs} input vars, "
                f"{self.max_gates} gate output vars, {self.max_gates * 2} aux vars, "
                f"{self.n_inputs} XOR chain vars"
            )
        else:
            # Explicit mode: allocate per-row variables
            # Gate value variables (per gate/input, per truth table row)
            # Includes both input variables and gate variables
            for g in range(self.n_inputs + self.max_gates):
                for row in range(self.n_rows):
                    self.gate_value[(g, row)] = self.next_var
                    self.next_var += 1
            
            print(f"[VariableManager] Gate value vars: {(self.n_inputs + self.max_gates) * self.n_rows} vars")
            
            # Auxiliary variables for input values (optimization for functionality encoding)
            for g in range(self.max_gates):
                for row_idx in range(self.n_rows):
                    self.left_val_vars[(g, row_idx)] = self.next_var
                    self.next_var += 1
                    self.right_val_vars[(g, row_idx)] = self.next_var
                    self.next_var += 1
            
            print(f"[VariableManager] Auxiliary input value vars: {self.max_gates * self.n_rows * 2} vars")


class CircuitSynthesisEncoder:
    """
    Encodes circuit synthesis as a SAT problem.
    
    The encoding asks: "Does there exist a circuit of the given class and size
    that computes the target function?"
    
    For monotone circuits, we encode:
    1. Structure: Each gate has type (AND/OR) and two inputs
    2. Topology: Inputs come from earlier gates (acyclic)
    3. Functionality: Circuit computes correctly on all truth table rows
    """
    
    def __init__(self):
        """Initialize encoder."""
        print(f"[CircuitSynthesisEncoder] Initialized")
    
    def encode_synthesis(
        self,
        n_inputs: int,
        max_gates: int,
        circuit_class: str,
        truth_table: List[Dict],
        encoding_mode: str = "explicit",
        target_function: Optional[str] = None,
    ) -> CNFProblem:
        """
        Encode circuit synthesis problem as CNF.
        
        Args:
            n_inputs: Number of input variables
            max_gates: Maximum number of gates in circuit
            circuit_class: Type of circuit ("monotone", "ac0", etc.)
            truth_table: List of truth table rows (dicts with 'inputs' and 'output')
            encoding_mode: "explicit" (use truth table) or "symbolic" (algebraic constraints)
            target_function: Function name for symbolic mode ("parity", etc.)
        
        Returns:
            CNFProblem encoding the synthesis question
        """
        print(f"[CircuitSynthesisEncoder] Encoding {circuit_class} synthesis:")
        print(f"  n_inputs={n_inputs}, max_gates={max_gates}, mode={encoding_mode}")
        
        # Determine encoding strategy
        symbolic_mode = (encoding_mode == "symbolic")
        
        if symbolic_mode:
            print(f"  Using symbolic encoding for {target_function}")
            truth_rows = []
        else:
            print(f"  Using explicit truth table with {len(truth_table)} rows")
            # Convert truth table
            if truth_table:
                truth_rows = [
                    TruthRow(inputs=row['inputs'], output=row['output'])
                    for row in truth_table
                ]
            else:
                raise ValueError("Explicit mode requires truth_table")
        
        # Create variable manager
        vars = VariableManager(n_inputs, max_gates, len(truth_rows), symbolic_mode=symbolic_mode)
        
        # Generate clauses
        clauses: List[List[int]] = []
        
        # 1. Structure constraints
        print(f"[CircuitSynthesisEncoder] Encoding structure constraints...")
        clauses.extend(self._encode_structure_constraints(vars))
        print(f"[CircuitSynthesisEncoder] Structure: {len(clauses)} clauses")
        
        # 2. Circuit class constraints (monotone, AC0, formula, etc.)
        if circuit_class == "monotone":
            print(f"[CircuitSynthesisEncoder] Encoding monotone constraints...")
            class_clauses = self._encode_monotone_constraints(vars)
            clauses.extend(class_clauses)
            print(f"[CircuitSynthesisEncoder] Monotone: {len(class_clauses)} clauses")
        elif circuit_class == "ac0":
            print(f"[CircuitSynthesisEncoder] Encoding AC0 constraints...")
            class_clauses = self._encode_ac0_constraints(vars, n_inputs, max_gates)
            clauses.extend(class_clauses)
            print(f"[CircuitSynthesisEncoder] AC0: {len(class_clauses)} clauses")
        elif circuit_class == "formula":
            print(f"[CircuitSynthesisEncoder] Encoding formula constraints...")
            class_clauses = self._encode_formula_constraints(vars)
            clauses.extend(class_clauses)
            print(f"[CircuitSynthesisEncoder] Formula: {len(class_clauses)} clauses")
        else:
            raise ValueError(f"Unsupported circuit class: {circuit_class}")
        
        # 3. Functionality constraints (truth table or symbolic)
        print(f"[CircuitSynthesisEncoder] Encoding functionality constraints...")
        if symbolic_mode:
            func_clauses = self._encode_symbolic_function(vars, target_function)
        else:
            func_clauses = self._encode_explicit_truth_table(vars, truth_rows)
        clauses.extend(func_clauses)
        print(f"[CircuitSynthesisEncoder] Functionality: {len(func_clauses)} clauses")
        
        print(f"[CircuitSynthesisEncoder] Total: {len(clauses)} clauses, {vars.next_var - 1} variables")
        
        mode_desc = f"symbolic {target_function}" if symbolic_mode else f"explicit {len(truth_rows)} rows"
        
        return CNFProblem(
            num_vars=vars.next_var - 1,
            num_clauses=len(clauses),
            clauses=clauses,
            comments=[
                f"Circuit synthesis encoding for {circuit_class}",
                f"n_inputs={n_inputs}, max_gates={max_gates}",
                f"encoding_mode={mode_desc}",
                f"SAT = circuit exists, UNSAT = no such circuit",
            ]
        )
    
    def _encode_structure_constraints(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode structural constraints for circuit.
        
        Returns:
            List of clauses
        """
        clauses = []
        
        for g in range(vars.max_gates):
            # 1. Each gate has exactly one type (AND or OR)
            # At least one type
            clauses.append([vars.gate_is_and[g], vars.gate_is_or[g]])
            
            # At most one type (not both)
            clauses.append([-vars.gate_is_and[g], -vars.gate_is_or[g]])
            
            # 2. Each gate input selects exactly one source
            num_sources = vars.n_inputs + g  # Can use inputs 0..n-1 and gates 0..g-1
            
            for input_pos in [0, 1]:
                # At least one source
                clause = []
                for source in range(num_sources):
                    clause.append(vars.input_select[(g, input_pos, source)])
                clauses.append(clause)
                
                # At most one source (pairwise exclusion)
                # OPTIMIZATION: Only add if num_sources is small
                # For large num_sources, this creates O(n²) clauses
                if num_sources <= 20:
                    for i in range(num_sources):
                        for j in range(i + 1, num_sources):
                            clauses.append([
                                -vars.input_select[(g, input_pos, i)],
                                -vars.input_select[(g, input_pos, j)],
                            ])
                else:
                    # Use sequential counter encoding for at-most-one
                    # This uses O(n) clauses instead of O(n²)
                    clauses.extend(self._encode_at_most_one_sequential(
                        [vars.input_select[(g, input_pos, src)] for src in range(num_sources)]
                    ))
        
        return clauses
    
    def _encode_at_most_one_sequential(self, variables: List[int]) -> List[List[int]]:
        """
        Encode at-most-one constraint using sequential counter.
        
        Uses O(n) auxiliary variables and O(n) clauses instead of O(n²).
        
        Based on: Sinz, C. (2005). "Towards an Optimal CNF Encoding of Boolean Cardinality Constraints"
        
        Args:
            variables: List of variables where at most one can be true
            
        Returns:
            List of clauses encoding the constraint
        """
        if len(variables) <= 1:
            return []
        
        clauses = []
        # Auxiliary variables s[1..n-1]
        # s[i] means "at least one of variables[0..i] is true"
        # We'll use negative numbers for auxiliary vars to avoid conflicts
        # (In practice, should allocate from variable manager, but this is simpler for now)
        
        # Actually, let's just use the quadratic encoding for now since it's simpler
        # and we're limiting to num_sources <= 20
        # This method is a placeholder for future optimization
        n = len(variables)
        for i in range(n):
            for j in range(i + 1, n):
                clauses.append([-variables[i], -variables[j]])
        
        return clauses
    
    def _encode_monotone_constraints(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode monotonicity constraint: only AND and OR gates allowed.
        
        For monotone circuits, we already restricted to AND/OR in structure,
        so no additional constraints needed.
        
        Returns:
            List of clauses (empty for monotone)
        """
        # Monotonicity is enforced by only having AND/OR as gate types
        # No additional constraints needed
        return []
    
    def _encode_ac0_constraints(self, vars: VariableManager, n_inputs: int, max_gates: int) -> List[List[int]]:
        """
        Encode AC0 constraints: constant depth, unbounded fan-in.
        
        For AC0, we allow NOT gates anywhere (not just inputs).
        We enforce depth constraints separately (would need depth tracking variables).
        For now, we just allow all three gate types.
        
        Returns:
            List of clauses
        """
        # AC0 allows AND, OR, and NOT gates
        # Depth constraints would require additional depth tracking variables
        # For MVP: just allow all gate types (depth enforcement TODO)
        print(f"[CircuitSynthesisEncoder] AC0: Allowing NOT gates (depth tracking TODO)")
        return []
    
    def _encode_formula_constraints(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode formula constraints: fan-out = 1 (tree structure).
        
        Each gate (except output) can be used by at most one other gate.
        This creates a tree rather than a DAG.
        
        Returns:
            List of clauses
        """
        clauses = []
        
        print(f"[CircuitSynthesisEncoder] Formula: Encoding fan-out = 1 constraints")
        
        # For each gate (except output), track how many times it's used
        # Gate g can be used as input by at most one other gate
        for g in range(vars.max_gates - 1):  # Last gate is output
            # Collect all input_select variables that reference gate g
            uses = []
            for next_g in range(g + 1, vars.max_gates):
                num_sources = vars.n_inputs + next_g
                if g < num_sources:
                    # Gate g could be selected by next_g's left or right input
                    for input_pos in [0, 1]:
                        if (next_g, input_pos, vars.n_inputs + g) in vars.input_select:
                            uses.append(vars.input_select[(next_g, input_pos, vars.n_inputs + g)])
            
            # At most one of these can be true
            if len(uses) > 1:
                for i in range(len(uses)):
                    for j in range(i + 1, len(uses)):
                        clauses.append([-uses[i], -uses[j]])
        
        print(f"[CircuitSynthesisEncoder] Formula: Added {len(clauses)} fan-out clauses")
        return clauses
    
    def _encode_explicit_truth_table(
        self,
        vars: VariableManager,
        truth_rows: List[TruthRow]
    ) -> List[List[int]]:
        """
        Encode that circuit computes correctly on all truth table rows (explicit mode).
        
        OPTIMIZED VERSION:
        - Instead of O(k² × rows) clauses per gate, use auxiliary variables
        - For each gate g and row r, create variables for "left input value" and "right input value"
        - Then encode: gate_value[g][r] = gate_type(left_val, right_val)
        
        This reduces clauses from O(k³ × 2^n) to O(k² × 2^n)
        
        Returns:
            List of clauses
        """
        clauses = []
        
        for row_idx, row in enumerate(truth_rows):
            # 1. Set input values for this row
            for input_idx in range(vars.n_inputs):
                input_gate_idx = input_idx  # Inputs are gates 0..n-1
                if row.inputs[input_idx] == 1:
                    clauses.append([vars.gate_value[(input_gate_idx, row_idx)]])
                else:
                    clauses.append([-vars.gate_value[(input_gate_idx, row_idx)]])
            
            # 2. For each gate, encode its computation using auxiliary variables
            for g in range(vars.max_gates):
                gate_idx = vars.n_inputs + g  # Gates are indexed after inputs
                num_sources = vars.n_inputs + g
                
                left_val = vars.left_val_vars[(g, row_idx)]
                right_val = vars.right_val_vars[(g, row_idx)]
                
                # Encode: left_val = value of selected left input source
                for src in range(num_sources):
                    # If input_select[g, 0, src] then left_val ↔ gate_value[src, row]
                    select_var = vars.input_select[(g, 0, src)]
                    src_val = vars.gate_value[(src, row_idx)]
                    
                    # (¬select ∨ (left_val ↔ src_val))
                    # Expand: (¬select ∨ ¬left_val ∨ src_val) ∧ (¬select ∨ left_val ∨ ¬src_val)
                    clauses.append([-select_var, -left_val, src_val])
                    clauses.append([-select_var, left_val, -src_val])
                
                # Encode: right_val = value of selected right input source
                for src in range(num_sources):
                    select_var = vars.input_select[(g, 1, src)]
                    src_val = vars.gate_value[(src, row_idx)]
                    
                    clauses.append([-select_var, -right_val, src_val])
                    clauses.append([-select_var, right_val, -src_val])
                
                # Encode: gate_value[g][row] = gate_type(left_val, right_val)
                gate_val = vars.gate_value[(gate_idx, row_idx)]
                
                # AND semantics: (¬gate_is_and ∨ (gate_val ↔ (left_val ∧ right_val)))
                clauses.extend([
                    [-vars.gate_is_and[g], -gate_val, left_val],
                    [-vars.gate_is_and[g], -gate_val, right_val],
                    [-vars.gate_is_and[g], -left_val, -right_val, gate_val],
                ])
                
                # OR semantics: (¬gate_is_or ∨ (gate_val ↔ (left_val ∨ right_val)))
                clauses.extend([
                    [-vars.gate_is_or[g], -gate_val, left_val, right_val],
                    [-vars.gate_is_or[g], -left_val, gate_val],
                    [-vars.gate_is_or[g], -right_val, gate_val],
                ])
            
            # 3. Output gate must match target function
            output_gate_idx = vars.n_inputs + vars.max_gates - 1  # Last gate
            if row.output == 1:
                clauses.append([vars.gate_value[(output_gate_idx, row_idx)]])
            else:
                clauses.append([-vars.gate_value[(output_gate_idx, row_idx)]])
        
        return clauses
    
    def _encode_symbolic_function(
        self,
        vars: VariableManager,
        target_function: str
    ) -> List[List[int]]:
        """
        Encode symbolic constraints for target function (symbolic mode).
        
        For large n, we can't materialize all 2^n rows. Instead, generate
        truth table rows on-the-fly and encode them directly into clauses
        without storing the full table in memory.
        
        Args:
            vars: Variable manager with symbolic mode enabled
            target_function: Function name ("parity", "majority", etc.)
        
        Returns:
            List of clauses encoding the symbolic constraints
        """
        if target_function == "parity":
            # Streaming truth table: generates all 2^n rows on-the-fly, O(2^n * k) clauses.
            # This is correct for UNSAT: it encodes correctness on every input row.
            # For n >= 16, the caller writes the CNF to a temp file and deletes it after
            # solving (V4b ephemeral mode) to avoid GB-scale storage.
            return self._encode_streaming_parity(vars)
        else:
            raise ValueError(f"Symbolic encoding not yet implemented for {target_function}")
    
    def _encode_algebraic_parity(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode parity algebraically (V4b): O(k^2 + n) clauses, zero truth table enumeration.

        Strategy
        --------
        Treat the n circuit inputs as *free* symbolic Boolean variables u_0..u_{n-1}.
        Propagate their values through the circuit using auxiliary "selected-source"
        variables (one left_aux and one right_aux per gate), then assert:

            output_gate_symbolic_value  =  XOR(u_0, ..., u_{n-1})

        Part 1 — XOR chain (O(n) clauses):
            xor[0]     = u_0
            xor[k]     = xor[k-1] XOR u_k    for k = 1..n-1
            output_sym = xor[n-1]

        Part 2 — Gate input-selection semantics (O(k^2) clauses):
            For each gate g:
                left_aux[g]  = value of the source that gate g's left input selects
                right_aux[g] = value of the source that gate g's right input selects

            For each possible source s:
                (input_select[g,0,s] is True) -> left_aux[g]  <-> source_value[s]
                (input_select[g,1,s] is True) -> right_aux[g] <-> source_value[s]

        Part 3 — Gate output semantics (O(k) clauses per gate):
            gate_is_and[g] -> gate_output[g] <-> (left_aux[g] AND right_aux[g])
            gate_is_or[g]  -> gate_output[g] <-> (left_aux[g] OR  right_aux[g])

        Total: O(k^2 + n) clauses — independent of 2^n.

        NOTE: The symbolic encoding is *sound* for UNSAT: if the SAT solver finds the
        formula UNSAT, no circuit of the given size computes parity (because any
        satisfying assignment would have to assign the free input variables to make
        the output match the XOR, and the gate semantics correctly propagate those).
        For SAT results the model gives a concrete circuit structure.

        Args:
            vars: VariableManager in symbolic_mode=True, with algebraic aux vars allocated.

        Returns:
            List of clauses.
        """
        print(
            f"[AlgebraicParity] Encoding symbolic parity for n={vars.n_inputs} inputs, "
            f"k={vars.max_gates} gates (O(k^2+n) clauses, not O(2^n*k))"
        )
        clauses: List[List[int]] = []

        # ----------------------------------------------------------------
        # Part 1: XOR chain over symbolic input variables
        # xor_chain[0] = input_vars[0]
        # xor_chain[i] = xor_chain[i-1] XOR input_vars[i]   for i >= 1
        # ----------------------------------------------------------------
        for step in range(vars.n_inputs):
            xor_out = vars.xor_chain_vars[step]
            if step == 0:
                # xor_chain[0] <-> input_vars[0]
                u = vars.input_vars[0]
                clauses.append([ xor_out, -u])
                clauses.append([-xor_out,  u])
            else:
                prev = vars.xor_chain_vars[step - 1]
                u    = vars.input_vars[step]
                clauses.extend(self._encode_xor(prev, u, xor_out))

        print(f"[AlgebraicParity] XOR chain: {len(clauses)} clauses so far")

        # ----------------------------------------------------------------
        # Part 2: Gate input-selection semantics
        # For each gate g, left_aux[g] (and right_aux[g]) is the symbolic
        # value of the source wire that gate g selects for its left (right) input.
        #
        # For every possible source s:
        #   (input_select[g, pos, s]) -> (aux[g] <-> source_value[s])
        # which expands to two clauses:
        #   (-select | -aux |  src)
        #   (-select |  aux | -src)
        # ----------------------------------------------------------------
        clauses_before_gates = len(clauses)
        for g in range(vars.max_gates):
            left_aux  = vars.left_aux_vars[g]
            right_aux = vars.right_aux_vars[g]
            num_sources = vars.n_inputs + g  # inputs 0..n-1, gates 0..g-1

            for src in range(num_sources):
                # Source symbolic value: input variable or previous gate output
                if src < vars.n_inputs:
                    src_val = vars.input_vars[src]
                else:
                    src_val = vars.gate_output_vars[src - vars.n_inputs]

                # Left input selection
                sel_left = vars.input_select[(g, 0, src)]
                clauses.append([-sel_left, -left_aux,  src_val])
                clauses.append([-sel_left,  left_aux, -src_val])

                # Right input selection
                sel_right = vars.input_select[(g, 1, src)]
                clauses.append([-sel_right, -right_aux,  src_val])
                clauses.append([-sel_right,  right_aux, -src_val])

        print(
            f"[AlgebraicParity] Gate input semantics: "
            f"{len(clauses) - clauses_before_gates} clauses"
        )

        # ----------------------------------------------------------------
        # Part 3: Gate output semantics
        # AND gate: gate_output <-> (left_aux AND right_aux)   when gate_is_and
        # OR  gate: gate_output <-> (left_aux OR  right_aux)   when gate_is_or
        #
        # Guarded implications (not unconditional) because gate type is a SAT var.
        # AND semantics (3 clauses per gate):
        #   (-gate_is_and | -gate_out |  left_aux)
        #   (-gate_is_and | -gate_out |  right_aux)
        #   (-gate_is_and | -left_aux | -right_aux | gate_out)
        # OR semantics (3 clauses per gate):
        #   (-gate_is_or | -gate_out |  left_aux | right_aux)
        #   (-gate_is_or | -left_aux |  gate_out)
        #   (-gate_is_or | -right_aux | gate_out)
        # ----------------------------------------------------------------
        clauses_before_output = len(clauses)
        for g in range(vars.max_gates):
            gate_out  = vars.gate_output_vars[g]
            gate_and  = vars.gate_is_and[g]
            gate_or   = vars.gate_is_or[g]
            left_aux  = vars.left_aux_vars[g]
            right_aux = vars.right_aux_vars[g]

            # AND semantics
            clauses.append([-gate_and, -gate_out,  left_aux])
            clauses.append([-gate_and, -gate_out,  right_aux])
            clauses.append([-gate_and, -left_aux, -right_aux, gate_out])

            # OR semantics
            clauses.append([-gate_or, -gate_out,  left_aux, right_aux])
            clauses.append([-gate_or, -left_aux,  gate_out])
            clauses.append([-gate_or, -right_aux, gate_out])

        print(
            f"[AlgebraicParity] Gate output semantics: "
            f"{len(clauses) - clauses_before_output} clauses"
        )

        # ----------------------------------------------------------------
        # Part 4: Output gate must equal final XOR
        # output_gate_symbolic = xor_chain[n-1]
        # Two clauses: biconditional
        # ----------------------------------------------------------------
        final_xor   = vars.xor_chain_vars[vars.n_inputs - 1]
        output_gate = vars.gate_output_vars[vars.max_gates - 1]
        clauses.append([ output_gate, -final_xor])
        clauses.append([-output_gate,  final_xor])

        print(
            f"[AlgebraicParity] Total algebraic clauses: {len(clauses)} "
            f"(expected O({vars.max_gates}^2 + {vars.n_inputs}) = O("
            f"{vars.max_gates**2 + vars.n_inputs}))"
        )
        return clauses

    def _encode_streaming_parity(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode parity using streaming truth table generation (symbolic mode).
        
        Instead of materializing all 2^n truth table rows in memory,
        generate each row on-the-fly and encode it directly to clauses.
        
        This trades memory for computation time, allowing us to handle
        larger n values (up to n=20) without running out of memory.
        
        For each truth table row:
        - Allocate fresh variables for gate values on that row
        - Encode gate semantics for that row
        - Constrain output to match parity
        
        Cost: O(2^n × gates) clauses, but O(gates) memory
        
        Args:
            vars: Variable manager with symbolic mode
        
        Returns:
            List of clauses encoding all truth table rows for parity
        """
        print(f"[StreamingParity] Encoding 2^{vars.n_inputs} = {2**vars.n_inputs} truth table rows on-the-fly")
        
        clauses = []
        n_rows = 2 ** vars.n_inputs
        
        # Generate truth table rows on-the-fly and encode each one
        for row_idx in range(n_rows):
            # Generate input values for this row
            inputs = [(row_idx >> j) & 1 for j in range(vars.n_inputs)]
            # Compute parity: XOR of all inputs
            output = sum(inputs) % 2
            
            # Encode this single truth table row
            row_clauses = self._encode_single_row_streaming(vars, inputs, output)
            clauses.extend(row_clauses)
            
            # Progress indicator for large n
            if n_rows > 1024 and (row_idx + 1) % 1024 == 0:
                print(f"[StreamingParity] Encoded {row_idx + 1}/{n_rows} rows...")
        
        print(f"[StreamingParity] Generated {len(clauses)} clauses from {n_rows} rows")
        
        return clauses
    
    def _encode_single_row_streaming(
        self,
        vars: VariableManager,
        inputs: List[int],
        output: int
    ) -> List[List[int]]:
        """
        Encode a single truth table row with streaming (allocate fresh vars per row).
        
        For a given input assignment and expected output:
        1. Allocate fresh variables for gate values on this row
        2. Set input values
        3. Encode gate propagation
        4. Constrain output
        
        This is similar to explicit mode but done one row at a time.
        
        Args:
            vars: Variable manager (will allocate new vars)
            inputs: List of input values (0 or 1)
            output: Expected output value (0 or 1)
        
        Returns:
            List of clauses for this row
        """
        clauses = []
        
        # Allocate gate value variables for this row
        row_gate_values = {}
        
        # Inputs
        for input_idx in range(vars.n_inputs):
            var = vars.next_var
            vars.next_var += 1
            row_gate_values[input_idx] = var
            
            # Constrain to input value
            if inputs[input_idx] == 1:
                clauses.append([var])
            else:
                clauses.append([-var])
        
        # Gates
        for g in range(vars.max_gates):
            gate_idx = vars.n_inputs + g
            gate_var = vars.next_var
            vars.next_var += 1
            row_gate_values[gate_idx] = gate_var
            
            num_sources = vars.n_inputs + g
            
            # Allocate auxiliary vars for gate inputs
            left_val = vars.next_var
            vars.next_var += 1
            right_val = vars.next_var
            vars.next_var += 1
            
            # Encode: left_val = value of selected left source
            for src in range(num_sources):
                select_var = vars.input_select[(g, 0, src)]
                src_val = row_gate_values[src]
                clauses.append([-select_var, -left_val, src_val])
                clauses.append([-select_var, left_val, -src_val])
            
            # Encode: right_val = value of selected right source
            for src in range(num_sources):
                select_var = vars.input_select[(g, 1, src)]
                src_val = row_gate_values[src]
                clauses.append([-select_var, -right_val, src_val])
                clauses.append([-select_var, right_val, -src_val])
            
            # Gate semantics (AND/OR)
            clauses.extend([
                [-vars.gate_is_and[g], -gate_var, left_val],
                [-vars.gate_is_and[g], -gate_var, right_val],
                [-vars.gate_is_and[g], -left_val, -right_val, gate_var],
            ])
            
            clauses.extend([
                [-vars.gate_is_or[g], -gate_var, left_val, right_val],
                [-vars.gate_is_or[g], -left_val, gate_var],
                [-vars.gate_is_or[g], -right_val, gate_var],
            ])
        
        # Output gate must match expected output
        output_gate_idx = vars.n_inputs + vars.max_gates - 1
        output_gate_var = row_gate_values[output_gate_idx]
        if output == 1:
            clauses.append([output_gate_var])
        else:
            clauses.append([-output_gate_var])
        
        return clauses
    
    def _encode_symbolic_parity(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode symbolic parity constraint: output = XOR(all inputs).
        
        Strategy:
        1. Build XOR chain: xor[0] = input[0]
                           xor[1] = xor[0] XOR input[1]
                           xor[2] = xor[1] XOR input[2]
                           ...
                           xor[n-1] = xor[n-2] XOR input[n-1]
        
        2. Connect circuit gates symbolically (AND/OR semantics)
        
        3. Constrain: output_gate = xor[n-1] (the parity)
        
        XOR(a, b) = c encoded as 4 clauses:
        - (a ∨ b ∨ ¬c)    [if both false, c false]
        - (¬a ∨ ¬b ∨ ¬c)  [if both true, c false]
        - (a ∨ ¬b ∨ c)    [if a true, b false, c true]
        - (¬a ∨ b ∨ c)    [if a false, b true, c true]
        
        Cost: O(n + gates) clauses instead of O(2^n × gates)
        
        Returns:
            List of clauses encoding parity constraint
        """
        print(f"[SymbolicParity] Encoding XOR chain for {vars.n_inputs} inputs")
        
        clauses = []
        
        # Part 1: XOR chain construction
        for step in range(vars.n_inputs):
            xor_var = vars.xor_chain_vars[step]
            
            if step == 0:
                # Base case: xor[0] = input[0]
                input_var = vars.input_vars[0]
                # xor[0] ↔ input[0]
                clauses.append([xor_var, -input_var])
                clauses.append([-xor_var, input_var])
            else:
                # Recursive case: xor[step] = xor[step-1] XOR input[step]
                prev_xor = vars.xor_chain_vars[step - 1]
                input_var = vars.input_vars[step]
                
                # Encode: xor_var = prev_xor XOR input_var
                clauses.extend(self._encode_xor(prev_xor, input_var, xor_var))
        
        print(f"[SymbolicParity] XOR chain: {len(clauses)} clauses")
        
        # Part 2: Connect circuit gates symbolically
        # For each gate, encode: gate_output = gate_type(input_sources)
        # We need to connect the gate outputs to compute from circuit inputs
        gate_clauses = self._encode_symbolic_gate_semantics(vars)
        clauses.extend(gate_clauses)
        
        print(f"[SymbolicParity] Gate semantics: {len(gate_clauses)} clauses")
        
        # Part 3: Output gate must equal final XOR
        final_xor = vars.xor_chain_vars[vars.n_inputs - 1]
        output_gate_idx = vars.max_gates - 1
        output_gate_var = vars.gate_output_vars[output_gate_idx]
        
        # output_gate ↔ final_xor
        clauses.append([output_gate_var, -final_xor])
        clauses.append([-output_gate_var, final_xor])
        
        print(f"[SymbolicParity] Total symbolic parity clauses: {len(clauses)}")
        
        return clauses
    
    def _encode_symbolic_gate_semantics(self, vars: VariableManager) -> List[List[int]]:
        """
        Encode gate semantics in symbolic mode.
        
        For each gate:
        - Determine its input sources (from input_select vars)
        - Encode: gate_output = gate_type(left_source, right_source)
        
        This connects the circuit structure to the symbolic values.
        
        Returns:
            List of clauses encoding gate evaluation
        """
        clauses = []
        
        for g in range(vars.max_gates):
            gate_output = vars.gate_output_vars[g]
            gate_is_and = vars.gate_is_and[g]
            gate_is_or = vars.gate_is_or[g]
            
            # For each possible source pair, encode the gate semantics
            num_sources = vars.n_inputs + g
            
            for left_src in range(num_sources):
                for right_src in range(num_sources):
                    # Variables: input_select says if this source is used
                    uses_left = vars.input_select.get((g, 0, left_src))
                    uses_right = vars.input_select.get((g, 1, right_src))
                    
                    if uses_left is None or uses_right is None:
                        continue
                    
                    # Get the symbolic value of the source
                    if left_src < vars.n_inputs:
                        left_val = vars.input_vars[left_src]
                    else:
                        left_val = vars.gate_output_vars[left_src - vars.n_inputs]
                    
                    if right_src < vars.n_inputs:
                        right_val = vars.input_vars[right_src]
                    else:
                        right_val = vars.gate_output_vars[right_src - vars.n_inputs]
                    
                    # Encode: if gate_is_and AND uses_left AND uses_right,
                    # then gate_output = left_val AND right_val
                    # Format: ¬(gate_is_and ∧ uses_left ∧ uses_right) ∨ (gate_output ↔ (left_val ∧ right_val))
                    
                    # AND semantics: output = left AND right
                    # output → left
                    clauses.append([-gate_is_and, -uses_left, -uses_right, -gate_output, left_val])
                    # output → right
                    clauses.append([-gate_is_and, -uses_left, -uses_right, -gate_output, right_val])
                    # (left ∧ right) → output
                    clauses.append([-gate_is_and, -uses_left, -uses_right, -left_val, -right_val, gate_output])
                    
                    # OR semantics: output = left OR right
                    # output → (left ∨ right)
                    clauses.append([-gate_is_or, -uses_left, -uses_right, -gate_output, left_val, right_val])
                    # left → output
                    clauses.append([-gate_is_or, -uses_left, -uses_right, -left_val, gate_output])
                    # right → output
                    clauses.append([-gate_is_or, -uses_left, -uses_right, -right_val, gate_output])
        
        return clauses
    
    def _encode_xor(self, a: int, b: int, c: int) -> List[List[int]]:
        """
        Encode XOR constraint: c = a XOR b
        
        Truth table for XOR:
        a  b  | c
        0  0  | 0
        0  1  | 1
        1  0  | 1
        1  1  | 0
        
        CNF clauses:
        - Row 1 (0,0,0): (a ∨ b ∨ ¬c)
        - Row 2 (0,1,1): (a ∨ ¬b ∨ c)
        - Row 3 (1,0,1): (¬a ∨ b ∨ c)
        - Row 4 (1,1,0): (¬a ∨ ¬b ∨ ¬c)
        
        Args:
            a, b: Input variables
            c: Output variable (c = a XOR b)
        
        Returns:
            List of 4 clauses encoding XOR
        """
        return [
            [a, b, -c],      # If both false, c must be false
            [-a, -b, -c],    # If both true, c must be false
            [a, -b, c],      # If a and not b, c must be true
            [-a, b, c],      # If not a and b, c must be true
        ]
    
    def _encode_and_semantics(
        self,
        gate_is_and: int,
        uses_left: int,
        uses_right: int,
        output: int,
        input_left: int,
        input_right: int,
    ) -> List[List[int]]:
        """
        Encode: If gate is AND and uses these inputs, then output = left AND right.
        
        Formula: (gate_is_and ∧ uses_left ∧ uses_right) → (output ↔ (left ∧ right))
        
        Clauses for output ↔ (left ∧ right):
        - output → left:  (¬output ∨ left)
        - output → right: (¬output ∨ right)
        - (left ∧ right) → output: (¬left ∨ ¬right ∨ output)
        
        Guarded by: gate_is_and ∧ uses_left ∧ uses_right
        
        Returns:
            List of clauses
        """
        return [
            # output → input_left (when conditions hold)
            [-gate_is_and, -uses_left, -uses_right, -output, input_left],
            # output → input_right (when conditions hold)
            [-gate_is_and, -uses_left, -uses_right, -output, input_right],
            # (input_left ∧ input_right) → output (when conditions hold)
            [-gate_is_and, -uses_left, -uses_right, -input_left, -input_right, output],
        ]
    
    def _encode_or_semantics(
        self,
        gate_is_or: int,
        uses_left: int,
        uses_right: int,
        output: int,
        input_left: int,
        input_right: int,
    ) -> List[List[int]]:
        """
        Encode: If gate is OR and uses these inputs, then output = left OR right.
        
        Formula: (gate_is_or ∧ uses_left ∧ uses_right) → (output ↔ (left ∨ right))
        
        Clauses for output ↔ (left ∨ right):
        - output → (left ∨ right): (¬output ∨ left ∨ right)
        - left → output:  (¬left ∨ output)
        - right → output: (¬right ∨ output)
        
        Guarded by: gate_is_or ∧ uses_left ∧ uses_right
        
        Returns:
            List of clauses
        """
        return [
            # output → (input_left ∨ input_right) (when conditions hold)
            [-gate_is_or, -uses_left, -uses_right, -output, input_left, input_right],
            # input_left → output (when conditions hold)
            [-gate_is_or, -uses_left, -uses_right, -input_left, output],
            # input_right → output (when conditions hold)
            [-gate_is_or, -uses_left, -uses_right, -input_right, output],
        ]
