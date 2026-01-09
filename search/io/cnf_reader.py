"""
CNF Reader - DIMACS format parser with comprehensive validation.

Parses CNF files in standard DIMACS format:
- Comments: Lines starting with 'c'
- Problem line: 'p cnf <num_vars> <num_clauses>'
- Clauses: Space-separated literals, terminated with 0
"""

from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple


@dataclass
class CNFProblem:
    """
    Represents a CNF problem instance.
    
    Attributes:
        num_vars: Number of variables (1-indexed)
        num_clauses: Number of clauses declared in problem line
        clauses: List of clauses (each clause is list of literals)
        comments: List of comment lines from file
    """
    num_vars: int
    num_clauses: int
    clauses: List[List[int]] = field(default_factory=list)
    comments: List[str] = field(default_factory=list)
    
    def validate(self) -> Tuple[bool, Optional[str]]:
        """
        Validate CNF problem integrity.
        
        Returns:
            Tuple of (is_valid, error_message)
        """
        # Log validation start
        print(f"[CNFProblem] Validating: {self.num_vars} vars, {self.num_clauses} clauses")
        
        # Check clause count matches declaration
        if len(self.clauses) != self.num_clauses:
            msg = f"Clause count mismatch: declared {self.num_clauses}, found {len(self.clauses)}"
            print(f"[CNFProblem] ERROR: {msg}")
            return False, msg
        
        # Check all literals are within variable range
        for idx, clause in enumerate(self.clauses):
            for lit in clause:
                if lit == 0:
                    msg = f"Clause {idx} contains zero (should be terminator only)"
                    print(f"[CNFProblem] ERROR: {msg}")
                    return False, msg
                
                var = abs(lit)
                if var > self.num_vars:
                    msg = f"Clause {idx} contains variable {var} > max {self.num_vars}"
                    print(f"[CNFProblem] ERROR: {msg}")
                    return False, msg
        
        print(f"[CNFProblem] Validation passed")
        return True, None
    
    def is_empty_clause_present(self) -> bool:
        """Check if any clause is empty (trivially UNSAT)."""
        return any(len(clause) == 0 for clause in self.clauses)
    
    def is_tautology_present(self) -> bool:
        """Check if any clause is a tautology (contains x and -x)."""
        for clause in self.clauses:
            literals_set = set(clause)
            for lit in literals_set:
                if -lit in literals_set:
                    return True
        return False
    
    def get_variables(self) -> set[int]:
        """Get set of all variables actually used in clauses."""
        variables = set()
        for clause in self.clauses:
            for lit in clause:
                variables.add(abs(lit))
        return variables


class CNFReader:
    """
    DIMACS CNF format reader with validation.
    
    Supports:
    - Standard DIMACS format
    - Comments (lines starting with 'c')
    - Whitespace tolerance
    - Validation of variable ranges
    """
    
    def __init__(self, strict: bool = True):
        """
        Initialize reader.
        
        Args:
            strict: If True, enforce strict validation (recommended)
        """
        self.strict = strict
        print(f"[CNFReader] Initialized (strict={strict})")
    
    def read(self, file_path: Path) -> CNFProblem:
        """
        Read CNF file and parse into CNFProblem.
        
        Args:
            file_path: Path to DIMACS CNF file
            
        Returns:
            CNFProblem instance
            
        Raises:
            FileNotFoundError: If file doesn't exist
            ValueError: If file format is invalid
        """
        print(f"[CNFReader] Reading file: {file_path}")
        
        if not file_path.exists():
            raise FileNotFoundError(f"CNF file not found: {file_path}")
        
        comments: List[str] = []
        clauses: List[List[int]] = []
        num_vars: Optional[int] = None
        num_clauses: Optional[int] = None
        problem_line_found = False
        
        with open(file_path, "r") as f:
            for line_num, line in enumerate(f, start=1):
                line = line.strip()
                
                # Log each line for debugging
                if line:
                    print(f"[CNFReader] Line {line_num}: {line[:50]}...")
                
                # Skip empty lines
                if not line:
                    continue
                
                # Parse comment lines
                if line.startswith("c"):
                    comment_text = line[1:].strip()
                    comments.append(comment_text)
                    print(f"[CNFReader] Comment: {comment_text[:40]}...")
                    continue
                
                # Parse problem line
                if line.startswith("p"):
                    if problem_line_found:
                        raise ValueError(f"Multiple 'p cnf' lines found (line {line_num})")
                    
                    parts = line.split()
                    if len(parts) < 4 or parts[0] != "p" or parts[1] != "cnf":
                        raise ValueError(f"Invalid problem line (line {line_num}): {line}")
                    
                    try:
                        num_vars = int(parts[2])
                        num_clauses = int(parts[3])
                        print(f"[CNFReader] Problem: {num_vars} vars, {num_clauses} clauses")
                    except ValueError as e:
                        raise ValueError(f"Invalid problem line numbers (line {line_num}): {e}")
                    
                    if num_vars < 0 or num_clauses < 0:
                        raise ValueError(f"Negative values in problem line (line {line_num})")
                    
                    problem_line_found = True
                    continue
                
                # Parse clause lines (must come after problem line)
                if not problem_line_found:
                    raise ValueError(f"Clause before problem line (line {line_num})")
                
                # Parse literals
                literals = []
                tokens = line.split()
                
                print(f"[CNFReader] Parsing clause with {len(tokens)} tokens")
                
                for token in tokens:
                    try:
                        lit = int(token)
                    except ValueError:
                        raise ValueError(f"Invalid literal '{token}' (line {line_num})")
                    
                    if lit == 0:
                        # End of clause (can be empty clause)
                        clauses.append(literals)
                        print(f"[CNFReader] Clause {len(clauses)}: {literals}")
                        literals = []
                    else:
                        literals.append(lit)
                
                # Handle clause not terminated with 0 (some parsers allow this at line end)
                if literals:
                    if self.strict:
                        raise ValueError(f"Clause not terminated with 0 (line {line_num})")
                    else:
                        clauses.append(literals)
                        print(f"[CNFReader] Clause {len(clauses)} (no terminator): {literals}")
        
        # Validate required problem line
        if not problem_line_found:
            raise ValueError("No 'p cnf' line found in file")
        
        print(f"[CNFReader] Parsed {len(clauses)} clauses")
        
        # Create problem instance
        problem = CNFProblem(
            num_vars=num_vars,
            num_clauses=num_clauses,
            clauses=clauses,
            comments=comments,
        )
        
        # Validate if strict mode
        if self.strict:
            is_valid, error_msg = problem.validate()
            if not is_valid:
                raise ValueError(f"CNF validation failed: {error_msg}")
        
        print(f"[CNFReader] Successfully parsed CNF: {num_vars} vars, {len(clauses)} clauses")
        return problem
    
    def read_from_string(self, content: str) -> CNFProblem:
        """
        Read CNF from string content.
        
        Args:
            content: DIMACS CNF format string
            
        Returns:
            CNFProblem instance
        """
        print(f"[CNFReader] Reading from string ({len(content)} bytes)")
        
        # Parse similar to file reading
        comments: List[str] = []
        clauses: List[List[int]] = []
        num_vars: Optional[int] = None
        num_clauses: Optional[int] = None
        problem_line_found = False
        
        for line_num, line in enumerate(content.split('\n'), start=1):
            line = line.strip()
            
            if not line:
                continue
            
            if line.startswith("c"):
                comments.append(line[1:].strip())
                continue
            
            if line.startswith("p"):
                if problem_line_found:
                    raise ValueError(f"Multiple 'p cnf' lines found (line {line_num})")
                
                parts = line.split()
                if len(parts) < 4 or parts[0] != "p" or parts[1] != "cnf":
                    raise ValueError(f"Invalid problem line (line {line_num}): {line}")
                
                num_vars = int(parts[2])
                num_clauses = int(parts[3])
                problem_line_found = True
                continue
            
            if not problem_line_found:
                raise ValueError(f"Clause before problem line (line {line_num})")
            
            # Parse literals
            literals = []
            tokens = line.split()
            
            for token in tokens:
                lit = int(token)
                if lit == 0:
                    if literals:
                        clauses.append(literals)
                        literals = []
                else:
                    literals.append(lit)
            
            if literals:
                if self.strict:
                    raise ValueError(f"Clause not terminated with 0 (line {line_num})")
                else:
                    clauses.append(literals)
        
        if not problem_line_found:
            raise ValueError("No 'p cnf' line found in content")
        
        problem = CNFProblem(
            num_vars=num_vars,
            num_clauses=num_clauses,
            clauses=clauses,
            comments=comments,
        )
        
        if self.strict:
            is_valid, error_msg = problem.validate()
            if not is_valid:
                raise ValueError(f"CNF validation failed: {error_msg}")
        
        return problem

