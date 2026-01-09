"""
CNF Writer - DIMACS format writer with formatting options.

Writes CNF problems in standard DIMACS format with:
- Proper header formatting
- Comment preservation
- Clean clause formatting
- Optional line wrapping
"""

from pathlib import Path
from typing import List, Optional
from .cnf_reader import CNFProblem


class CNFWriter:
    """
    DIMACS CNF format writer.
    
    Supports:
    - Standard DIMACS format
    - Comment injection
    - Configurable formatting
    - Validation before writing
    """
    
    def __init__(self, line_width: int = 80, validate: bool = True):
        """
        Initialize writer.
        
        Args:
            line_width: Maximum line width for clause wrapping (0 = no wrapping)
            validate: If True, validate problem before writing
        """
        self.line_width = line_width
        self.validate = validate
        print(f"[CNFWriter] Initialized (line_width={line_width}, validate={validate})")
    
    def write(
        self, 
        problem: CNFProblem, 
        file_path: Path,
        additional_comments: Optional[List[str]] = None
    ) -> None:
        """
        Write CNF problem to file in DIMACS format.
        
        Args:
            problem: CNFProblem instance to write
            file_path: Output file path
            additional_comments: Optional extra comments to prepend
            
        Raises:
            ValueError: If problem validation fails
        """
        print(f"[CNFWriter] Writing to file: {file_path}")
        
        # Validate problem if requested
        if self.validate:
            is_valid, error_msg = problem.validate()
            if not is_valid:
                raise ValueError(f"Cannot write invalid CNF: {error_msg}")
        
        # Create parent directory if needed
        file_path.parent.mkdir(parents=True, exist_ok=True)
        
        # Write to file
        with open(file_path, "w") as f:
            content = self.to_string(problem, additional_comments)
            f.write(content)
            print(f"[CNFWriter] Wrote {len(content)} bytes")
        
        print(f"[CNFWriter] Successfully wrote CNF to {file_path}")
    
    def to_string(
        self, 
        problem: CNFProblem,
        additional_comments: Optional[List[str]] = None
    ) -> str:
        """
        Convert CNF problem to DIMACS format string.
        
        Args:
            problem: CNFProblem instance
            additional_comments: Optional extra comments to prepend
            
        Returns:
            DIMACS format string
        """
        print(f"[CNFWriter] Converting to string: {problem.num_vars} vars, {len(problem.clauses)} clauses")
        
        lines: List[str] = []
        
        # Write additional comments first
        if additional_comments:
            for comment in additional_comments:
                lines.append(f"c {comment}")
                print(f"[CNFWriter] Added comment: {comment[:40]}...")
        
        # Write original comments
        for comment in problem.comments:
            lines.append(f"c {comment}")
        
        # Write problem line
        problem_line = f"p cnf {problem.num_vars} {problem.num_clauses}"
        lines.append(problem_line)
        print(f"[CNFWriter] Problem line: {problem_line}")
        
        # Write clauses
        for idx, clause in enumerate(problem.clauses):
            clause_str = self._format_clause(clause)
            lines.append(clause_str)
            
            if (idx + 1) % 100 == 0:
                print(f"[CNFWriter] Wrote {idx + 1}/{len(problem.clauses)} clauses...")
        
        print(f"[CNFWriter] Formatted {len(problem.clauses)} clauses")
        
        # Join with newlines and ensure trailing newline
        content = '\n'.join(lines) + '\n'
        return content
    
    def _format_clause(self, clause: List[int]) -> str:
        """
        Format a single clause with optional line wrapping.
        
        Args:
            clause: List of literals
            
        Returns:
            Formatted clause string (without newline)
        """
        # Build clause string with 0 terminator
        literals_str = ' '.join(str(lit) for lit in clause) + ' 0'
        
        # Apply line wrapping if needed
        if self.line_width > 0 and len(literals_str) > self.line_width:
            # Wrap long clauses (rare in practice)
            wrapped = self._wrap_line(literals_str)
            return wrapped
        
        return literals_str
    
    def _wrap_line(self, line: str) -> str:
        """
        Wrap long line at word boundaries.
        
        Args:
            line: Long line to wrap
            
        Returns:
            Wrapped line (may contain line continuations)
        """
        # For DIMACS, we don't actually wrap - just return as-is
        # Line wrapping would require continuation syntax which is non-standard
        # Most parsers handle arbitrarily long lines
        return line
    
    def write_clauses_only(
        self,
        clauses: List[List[int]],
        num_vars: int,
        file_path: Path,
        comments: Optional[List[str]] = None
    ) -> None:
        """
        Convenience method to write clauses directly without CNFProblem.
        
        Args:
            clauses: List of clauses (each clause is list of literals)
            num_vars: Number of variables
            file_path: Output file path
            comments: Optional comments
        """
        print(f"[CNFWriter] Writing {len(clauses)} clauses directly")
        
        # Create CNFProblem instance
        problem = CNFProblem(
            num_vars=num_vars,
            num_clauses=len(clauses),
            clauses=clauses,
            comments=comments or [],
        )
        
        # Write using standard method
        self.write(problem, file_path)


def write_cnf(
    clauses: List[List[int]],
    num_vars: int,
    file_path: Path,
    comments: Optional[List[str]] = None
) -> None:
    """
    Quick utility function to write CNF without creating writer instance.
    
    Args:
        clauses: List of clauses
        num_vars: Number of variables
        file_path: Output file path
        comments: Optional comments
    """
    writer = CNFWriter()
    writer.write_clauses_only(clauses, num_vars, file_path, comments)

