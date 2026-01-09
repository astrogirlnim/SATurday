"""
Unit tests for CNF I/O (reader and writer).

Tests:
- DIMACS parsing
- CNF writing
- Round-trip preservation
- Edge cases (empty clauses, tautologies)
- Validation
"""

import pytest
from pathlib import Path
import tempfile
import shutil

# Add parent directory to path for imports
import sys
parent_dir = Path(__file__).parent.parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from search.io.cnf_reader import CNFReader, CNFProblem
from search.io.cnf_writer import CNFWriter, write_cnf


class TestCNFReader:
    """Test CNFReader functionality."""
    
    @pytest.fixture
    def fixtures_dir(self) -> Path:
        """Get fixtures directory path."""
        return Path(__file__).parent / "fixtures"
    
    @pytest.fixture
    def reader(self) -> CNFReader:
        """Create CNFReader instance."""
        return CNFReader(strict=True)
    
    def test_read_simple_sat(self, reader: CNFReader, fixtures_dir: Path):
        """Test reading simple SAT instance."""
        print("\n[TEST] test_read_simple_sat")
        cnf_file = fixtures_dir / "simple_sat.cnf"
        
        problem = reader.read(cnf_file)
        
        assert problem.num_vars == 1
        assert problem.num_clauses == 1
        assert len(problem.clauses) == 1
        assert problem.clauses[0] == [1]
        assert len(problem.comments) >= 1
        print("[TEST] simple_sat: PASS")
    
    def test_read_simple_unsat(self, reader: CNFReader, fixtures_dir: Path):
        """Test reading simple UNSAT instance."""
        print("\n[TEST] test_read_simple_unsat")
        cnf_file = fixtures_dir / "simple_unsat.cnf"
        
        problem = reader.read(cnf_file)
        
        assert problem.num_vars == 1
        assert problem.num_clauses == 2
        assert len(problem.clauses) == 2
        assert problem.clauses[0] == [1]
        assert problem.clauses[1] == [-1]
        print("[TEST] simple_unsat: PASS")
    
    def test_read_multivar(self, reader: CNFReader, fixtures_dir: Path):
        """Test reading multi-variable instance."""
        print("\n[TEST] test_read_multivar")
        cnf_file = fixtures_dir / "multivar.cnf"
        
        problem = reader.read(cnf_file)
        
        assert problem.num_vars == 5
        assert problem.num_clauses == 8
        assert len(problem.clauses) == 8
        
        # Check first clause
        assert problem.clauses[0] == [1, 2, 3]
        
        # Check last clause
        assert problem.clauses[7] == [-4, -5, -1]
        
        # Check all variables are in range
        variables = problem.get_variables()
        assert all(1 <= v <= 5 for v in variables)
        print("[TEST] multivar: PASS")
    
    def test_detect_tautology(self, reader: CNFReader, fixtures_dir: Path):
        """Test tautology detection."""
        print("\n[TEST] test_detect_tautology")
        cnf_file = fixtures_dir / "tautology.cnf"
        
        problem = reader.read(cnf_file)
        
        assert problem.is_tautology_present()
        print("[TEST] tautology: PASS")
    
    def test_detect_empty_clause(self, reader: CNFReader, fixtures_dir: Path):
        """Test empty clause detection."""
        print("\n[TEST] test_detect_empty_clause")
        cnf_file = fixtures_dir / "empty_clause.cnf"
        
        # Empty clause should parse (it's a valid clause in strict mode)
        problem = reader.read(cnf_file)
        
        assert problem.is_empty_clause_present()
        print("[TEST] empty_clause: PASS")
    
    def test_read_from_string(self, reader: CNFReader):
        """Test reading from string content."""
        print("\n[TEST] test_read_from_string")
        content = """c Test CNF
p cnf 2 2
1 2 0
-1 -2 0
"""
        problem = reader.read_from_string(content)
        
        assert problem.num_vars == 2
        assert problem.num_clauses == 2
        assert len(problem.clauses) == 2
        assert problem.clauses[0] == [1, 2]
        assert problem.clauses[1] == [-1, -2]
        print("[TEST] read_from_string: PASS")
    
    def test_validation(self, reader: CNFReader):
        """Test CNF validation."""
        print("\n[TEST] test_validation")
        
        # Valid problem
        problem = CNFProblem(
            num_vars=2,
            num_clauses=1,
            clauses=[[1, -2]],
        )
        is_valid, error = problem.validate()
        assert is_valid
        assert error is None
        
        # Invalid: clause count mismatch
        problem_bad = CNFProblem(
            num_vars=2,
            num_clauses=5,  # Claims 5 but has 1
            clauses=[[1, -2]],
        )
        is_valid, error = problem_bad.validate()
        assert not is_valid
        assert "mismatch" in error.lower()
        
        print("[TEST] validation: PASS")
    
    def test_invalid_variable_range(self, reader: CNFReader):
        """Test detection of out-of-range variables."""
        print("\n[TEST] test_invalid_variable_range")
        
        problem = CNFProblem(
            num_vars=2,
            num_clauses=1,
            clauses=[[1, -5]],  # Variable 5 > num_vars=2
        )
        
        is_valid, error = problem.validate()
        assert not is_valid
        assert "5" in error
        assert "2" in error
        print("[TEST] invalid_variable_range: PASS")


class TestCNFWriter:
    """Test CNFWriter functionality."""
    
    @pytest.fixture
    def writer(self) -> CNFWriter:
        """Create CNFWriter instance."""
        return CNFWriter(validate=True)
    
    @pytest.fixture
    def temp_dir(self):
        """Create temporary directory for test outputs."""
        temp = Path(tempfile.mkdtemp())
        yield temp
        # Cleanup
        shutil.rmtree(temp)
    
    def test_write_simple(self, writer: CNFWriter, temp_dir: Path):
        """Test writing simple CNF."""
        print("\n[TEST] test_write_simple")
        
        problem = CNFProblem(
            num_vars=2,
            num_clauses=2,
            clauses=[[1, 2], [-1, -2]],
            comments=["Test problem"],
        )
        
        output_file = temp_dir / "test.cnf"
        writer.write(problem, output_file)
        
        assert output_file.exists()
        
        # Read back and verify
        content = output_file.read_text()
        assert "p cnf 2 2" in content
        assert "1 2 0" in content
        assert "-1 -2 0" in content
        assert "c Test problem" in content
        print("[TEST] write_simple: PASS")
    
    def test_write_with_additional_comments(self, writer: CNFWriter, temp_dir: Path):
        """Test writing with additional comments."""
        print("\n[TEST] test_write_with_additional_comments")
        
        problem = CNFProblem(
            num_vars=1,
            num_clauses=1,
            clauses=[[1]],
        )
        
        output_file = temp_dir / "commented.cnf"
        writer.write(problem, output_file, additional_comments=["Generated by test"])
        
        content = output_file.read_text()
        assert "c Generated by test" in content
        print("[TEST] write_with_additional_comments: PASS")
    
    def test_write_clauses_only(self, writer: CNFWriter, temp_dir: Path):
        """Test convenience method for writing clauses directly."""
        print("\n[TEST] test_write_clauses_only")
        
        clauses = [[1, 2], [-1], [2, -3]]
        num_vars = 3
        output_file = temp_dir / "direct.cnf"
        
        writer.write_clauses_only(clauses, num_vars, output_file, comments=["Direct write"])
        
        assert output_file.exists()
        content = output_file.read_text()
        assert "p cnf 3 3" in content
        assert "c Direct write" in content
        print("[TEST] write_clauses_only: PASS")
    
    def test_write_utility_function(self, temp_dir: Path):
        """Test write_cnf utility function."""
        print("\n[TEST] test_write_utility_function")
        
        clauses = [[1], [-1]]
        output_file = temp_dir / "utility.cnf"
        
        write_cnf(clauses, 1, output_file, comments=["Utility test"])
        
        assert output_file.exists()
        print("[TEST] write_utility_function: PASS")


class TestRoundTrip:
    """Test round-trip preservation (read -> write -> read)."""
    
    @pytest.fixture
    def fixtures_dir(self) -> Path:
        """Get fixtures directory path."""
        return Path(__file__).parent / "fixtures"
    
    @pytest.fixture
    def temp_dir(self):
        """Create temporary directory for test outputs."""
        temp = Path(tempfile.mkdtemp())
        yield temp
        shutil.rmtree(temp)
    
    def test_roundtrip_simple_sat(self, fixtures_dir: Path, temp_dir: Path):
        """Test round-trip for simple SAT instance."""
        print("\n[TEST] test_roundtrip_simple_sat")
        
        # Read original
        reader = CNFReader(strict=True)
        original = reader.read(fixtures_dir / "simple_sat.cnf")
        
        # Write to temp file
        writer = CNFWriter(validate=True)
        temp_file = temp_dir / "roundtrip.cnf"
        writer.write(original, temp_file)
        
        # Read back
        reread = reader.read(temp_file)
        
        # Verify preservation
        assert reread.num_vars == original.num_vars
        assert reread.num_clauses == original.num_clauses
        assert reread.clauses == original.clauses
        print("[TEST] roundtrip_simple_sat: PASS")
    
    def test_roundtrip_multivar(self, fixtures_dir: Path, temp_dir: Path):
        """Test round-trip for multi-variable instance."""
        print("\n[TEST] test_roundtrip_multivar")
        
        reader = CNFReader(strict=True)
        writer = CNFWriter(validate=True)
        
        # Read original
        original = reader.read(fixtures_dir / "multivar.cnf")
        
        # Write and read back
        temp_file = temp_dir / "multivar_roundtrip.cnf"
        writer.write(original, temp_file)
        reread = reader.read(temp_file)
        
        # Verify exact preservation of clauses
        assert reread.clauses == original.clauses
        assert reread.num_vars == original.num_vars
        assert reread.num_clauses == original.num_clauses
        print("[TEST] roundtrip_multivar: PASS")
    
    def test_roundtrip_preserves_semantics(self, fixtures_dir: Path, temp_dir: Path):
        """Test that round-trip preserves semantic meaning."""
        print("\n[TEST] test_roundtrip_preserves_semantics")
        
        reader = CNFReader(strict=True)
        writer = CNFWriter(validate=True)
        
        # Read simple UNSAT
        original = reader.read(fixtures_dir / "simple_unsat.cnf")
        
        # Multiple round-trips
        current_file = temp_dir / "trip1.cnf"
        writer.write(original, current_file)
        
        for i in range(3):
            print(f"[TEST] Round-trip iteration {i+1}")
            problem = reader.read(current_file)
            next_file = temp_dir / f"trip{i+2}.cnf"
            writer.write(problem, next_file)
            current_file = next_file
        
        # Final read
        final = reader.read(current_file)
        
        # Should be identical to original
        assert final.clauses == original.clauses
        assert final.num_vars == original.num_vars
        print("[TEST] roundtrip_preserves_semantics: PASS")
    
    def test_roundtrip_programmatic(self, temp_dir: Path):
        """Test round-trip for programmatically created CNF."""
        print("\n[TEST] test_roundtrip_programmatic")
        
        # Create problem programmatically
        clauses = [
            [1, 2, 3],
            [-1, 2],
            [-2, 3],
            [-3],
        ]
        
        problem = CNFProblem(
            num_vars=3,
            num_clauses=4,
            clauses=clauses,
            comments=["Programmatic test"],
        )
        
        # Write
        writer = CNFWriter()
        temp_file = temp_dir / "programmatic.cnf"
        writer.write(problem, temp_file)
        
        # Read back
        reader = CNFReader()
        reread = reader.read(temp_file)
        
        # Verify
        assert reread.clauses == clauses
        assert reread.num_vars == 3
        assert reread.num_clauses == 4
        print("[TEST] roundtrip_programmatic: PASS")


if __name__ == "__main__":
    print("=" * 60)
    print("CNF I/O Test Suite")
    print("=" * 60)
    
    # Run pytest
    pytest.main([__file__, "-v", "--tb=short"])

