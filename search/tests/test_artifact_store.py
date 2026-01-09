"""
Unit tests for the artifact store system.

Tests cover:
1. Store initialization and index persistence
2. Artifact registration with metadata
3. Querying artifacts by properties
4. Integrity verification
5. Lineage tracking (parents and children)
6. Store statistics
"""

import json
import tempfile
from pathlib import Path

import pytest

from search.tools.artifact_store import ArtifactStore, ArtifactType, ArtifactMetadata


class TestArtifactStoreBasics:
    """Test basic store operations."""
    
    def test_store_initialization(self):
        """Test store creation and initialization."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            
            print(f"\n[Test] Creating store at {store_dir}")
            store = ArtifactStore(store_dir)
            
            # Check directory created
            assert store_dir.exists()
            
            # Check store is empty (index file created on first save)
            assert len(store.index) == 0
            
            print(f"[Test] Store initialized successfully")
    
    def test_index_persistence(self):
        """Test that index persists across store instances."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            
            # Create test file
            test_file = store_dir / "test.txt"
            test_file.write_text("Hello, world!")
            
            print(f"\n[Test] Registering artifact in first store instance")
            
            # Register artifact in first store
            store1 = ArtifactStore(store_dir)
            metadata1 = store1.register(
                file_path=test_file,
                artifact_type=ArtifactType.METADATA,
                tool_name="test",
                copy_to_store=False,
            )
            
            artifact_hash = metadata1.artifact_hash
            print(f"[Test] Registered artifact: {artifact_hash[:16]}...")
            
            # Create new store instance
            print(f"[Test] Loading store in second instance")
            store2 = ArtifactStore(store_dir)
            
            # Check artifact exists in new instance
            assert artifact_hash in store2.index
            metadata2 = store2.get(artifact_hash)
            assert metadata2 is not None
            assert metadata2.artifact_hash == artifact_hash
            assert metadata2.artifact_type == ArtifactType.METADATA
            
            print(f"[Test] Index persisted successfully")


class TestArtifactRegistration:
    """Test artifact registration."""
    
    def test_register_simple_artifact(self):
        """Test registering a simple artifact."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            # Create test file
            test_file = Path(tmpdir) / "test.cnf"
            test_file.write_text("p cnf 2 1\n1 2 0\n")
            
            print(f"\n[Test] Registering CNF artifact")
            
            # Register artifact
            metadata = store.register(
                file_path=test_file,
                artifact_type=ArtifactType.CNF,
                tool_name="test",
                tool_version="1.0.0",
                copy_to_store=False,
            )
            
            # Check metadata
            assert metadata.artifact_hash is not None
            assert metadata.artifact_type == ArtifactType.CNF
            assert metadata.tool_name == "test"
            assert metadata.tool_version == "1.0.0"
            assert metadata.verified is True
            
            # Check in index
            assert metadata.artifact_hash in store.index
            
            print(f"[Test] Artifact registered: {metadata.artifact_hash[:16]}...")
    
    def test_register_with_lineage(self):
        """Test registering artifacts with parent lineage."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            # Register parent artifact
            parent_file = Path(tmpdir) / "parent.cnf"
            parent_file.write_text("p cnf 2 1\n1 2 0\n")
            
            print(f"\n[Test] Registering parent artifact")
            parent_metadata = store.register(
                file_path=parent_file,
                artifact_type=ArtifactType.CNF,
                tool_name="test",
                copy_to_store=False,
            )
            
            parent_hash = parent_metadata.artifact_hash
            print(f"[Test] Parent: {parent_hash[:16]}...")
            
            # Register child artifact
            child_file = Path(tmpdir) / "child.lrat"
            child_file.write_text("0")
            
            print(f"[Test] Registering child artifact with lineage")
            child_metadata = store.register(
                file_path=child_file,
                artifact_type=ArtifactType.LRAT,
                tool_name="kissat",
                parent_hashes=[parent_hash],
                copy_to_store=False,
            )
            
            # Check lineage
            assert len(child_metadata.parent_hashes) == 1
            assert child_metadata.parent_hashes[0] == parent_hash
            
            print(f"[Test] Child: {child_metadata.artifact_hash[:16]}...")
            print(f"[Test] Lineage preserved")
    
    def test_register_with_properties(self):
        """Test registering artifacts with custom properties."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            # Create test file
            test_file = Path(tmpdir) / "circuit.json"
            test_file.write_text('{"gates": 10}')
            
            print(f"\n[Test] Registering artifact with custom properties")
            
            # Register with properties
            metadata = store.register(
                file_path=test_file,
                artifact_type=ArtifactType.CIRCUIT,
                tool_name="circuit_builder",
                properties={
                    "num_gates": 10,
                    "depth": 3,
                    "circuit_type": "monotone",
                },
                copy_to_store=False,
            )
            
            # Check properties
            assert metadata.properties["num_gates"] == 10
            assert metadata.properties["depth"] == 3
            assert metadata.properties["circuit_type"] == "monotone"
            
            print(f"[Test] Properties stored: {metadata.properties}")
    
    def test_register_duplicate_ignored(self):
        """Test that registering same artifact twice is idempotent."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            # Create test file
            test_file = Path(tmpdir) / "test.txt"
            test_file.write_text("Same content")
            
            print(f"\n[Test] Registering artifact twice")
            
            # Register first time
            metadata1 = store.register(
                file_path=test_file,
                artifact_type=ArtifactType.METADATA,
                tool_name="test",
                copy_to_store=False,
            )
            
            # Register second time (should return existing)
            metadata2 = store.register(
                file_path=test_file,
                artifact_type=ArtifactType.METADATA,
                tool_name="test",
                copy_to_store=False,
            )
            
            # Check same hash
            assert metadata1.artifact_hash == metadata2.artifact_hash
            
            # Check only one entry in index
            assert len(store.index) == 1
            
            print(f"[Test] Duplicate registration handled correctly")


class TestArtifactQuerying:
    """Test artifact querying and filtering."""
    
    def test_query_by_type(self):
        """Test querying artifacts by type."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating multiple artifact types")
            
            # Register multiple artifacts of different types
            for i, artifact_type in enumerate([ArtifactType.CNF, ArtifactType.LRAT, ArtifactType.CNF]):
                test_file = Path(tmpdir) / f"test{i}.txt"
                test_file.write_text(f"Content {i}")
                
                store.register(
                    file_path=test_file,
                    artifact_type=artifact_type,
                    tool_name="test",
                    copy_to_store=False,
                )
            
            # Query by type
            print(f"[Test] Querying for CNF artifacts")
            cnf_artifacts = store.query(artifact_type=ArtifactType.CNF)
            
            assert len(cnf_artifacts) == 2
            for artifact in cnf_artifacts:
                assert artifact.artifact_type == ArtifactType.CNF
            
            print(f"[Test] Found {len(cnf_artifacts)} CNF artifacts")
    
    def test_query_by_tool(self):
        """Test querying artifacts by tool name."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating artifacts from different tools")
            
            # Register artifacts from different tools
            for i, tool_name in enumerate(["kissat", "test", "kissat"]):
                test_file = Path(tmpdir) / f"test{i}.txt"
                test_file.write_text(f"Content {i}")
                
                store.register(
                    file_path=test_file,
                    artifact_type=ArtifactType.SOLVER_LOG,
                    tool_name=tool_name,
                    copy_to_store=False,
                )
            
            # Query by tool
            print(f"[Test] Querying for kissat artifacts")
            kissat_artifacts = store.query(tool_name="kissat")
            
            assert len(kissat_artifacts) == 2
            for artifact in kissat_artifacts:
                assert artifact.tool_name == "kissat"
            
            print(f"[Test] Found {len(kissat_artifacts)} kissat artifacts")
    
    def test_query_by_parent(self):
        """Test querying artifacts by parent hash."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating parent-child artifacts")
            
            # Register parent
            parent_file = Path(tmpdir) / "parent.cnf"
            parent_file.write_text("Parent content")
            parent = store.register(
                file_path=parent_file,
                artifact_type=ArtifactType.CNF,
                tool_name="test",
                copy_to_store=False,
            )
            
            # Register children
            for i in range(3):
                child_file = Path(tmpdir) / f"child{i}.lrat"
                child_file.write_text(f"Child {i}")
                
                store.register(
                    file_path=child_file,
                    artifact_type=ArtifactType.LRAT,
                    tool_name="kissat",
                    parent_hashes=[parent.artifact_hash],
                    copy_to_store=False,
                )
            
            # Query by parent
            print(f"[Test] Querying for children of parent")
            children = store.query(parent_hash=parent.artifact_hash)
            
            assert len(children) == 3
            for child in children:
                assert parent.artifact_hash in child.parent_hashes
            
            print(f"[Test] Found {len(children)} children")
    
    def test_query_by_properties(self):
        """Test querying artifacts by custom properties."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating artifacts with properties")
            
            # Register artifacts with properties
            for i in range(3):
                test_file = Path(tmpdir) / f"test{i}.json"
                test_file.write_text(f'{{"id": {i}}}')
                
                store.register(
                    file_path=test_file,
                    artifact_type=ArtifactType.CIRCUIT,
                    tool_name="test",
                    properties={"status": "SAT" if i % 2 == 0 else "UNSAT"},
                    copy_to_store=False,
                )
            
            # Query by property
            print(f"[Test] Querying for SAT artifacts")
            sat_artifacts = store.query(properties={"status": "SAT"})
            
            assert len(sat_artifacts) == 2
            for artifact in sat_artifacts:
                assert artifact.properties["status"] == "SAT"
            
            print(f"[Test] Found {len(sat_artifacts)} SAT artifacts")


class TestArtifactVerification:
    """Test artifact integrity verification."""
    
    def test_verify_artifact(self):
        """Test verifying a single artifact."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            # Create and register artifact
            test_file = Path(tmpdir) / "test.txt"
            test_file.write_text("Original content")
            
            print(f"\n[Test] Registering and verifying artifact")
            
            metadata = store.register(
                file_path=test_file,
                artifact_type=ArtifactType.METADATA,
                tool_name="test",
                copy_to_store=False,
            )
            
            # Verify (should pass)
            assert store.verify(metadata.artifact_hash) is True
            assert metadata.verified is True
            
            print(f"[Test] Verification passed")
    
    def test_verify_modified_artifact(self):
        """Test that verification fails for modified artifacts."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            # Create and register artifact
            test_file = Path(tmpdir) / "test.txt"
            test_file.write_text("Original content")
            
            print(f"\n[Test] Registering artifact")
            
            metadata = store.register(
                file_path=test_file,
                artifact_type=ArtifactType.METADATA,
                tool_name="test",
                copy_to_store=False,
            )
            
            # Modify file
            print(f"[Test] Modifying artifact file")
            test_file.write_text("Modified content")
            
            # Verify (should fail)
            print(f"[Test] Verifying modified artifact")
            assert store.verify(metadata.artifact_hash) is False
            assert metadata.verified is False
            
            print(f"[Test] Verification correctly failed for modified artifact")
    
    def test_verify_all(self):
        """Test verifying all artifacts in store."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating multiple artifacts")
            
            # Register multiple artifacts
            artifacts = []
            for i in range(3):
                test_file = Path(tmpdir) / f"test{i}.txt"
                test_file.write_text(f"Content {i}")
                
                metadata = store.register(
                    file_path=test_file,
                    artifact_type=ArtifactType.METADATA,
                    tool_name="test",
                    copy_to_store=False,
                )
                artifacts.append((test_file, metadata))
            
            # Verify all (should all pass)
            print(f"[Test] Verifying all artifacts")
            results = store.verify_all()
            
            assert len(results) == 3
            assert all(results.values())
            
            print(f"[Test] All verifications passed")


class TestArtifactLineage:
    """Test lineage tracking."""
    
    def test_get_lineage(self):
        """Test getting full lineage of an artifact."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating artifact chain")
            
            # Create chain: A -> B -> C
            file_a = Path(tmpdir) / "a.txt"
            file_a.write_text("A")
            meta_a = store.register(
                file_path=file_a,
                artifact_type=ArtifactType.CNF,
                tool_name="test",
                copy_to_store=False,
            )
            
            file_b = Path(tmpdir) / "b.txt"
            file_b.write_text("B")
            meta_b = store.register(
                file_path=file_b,
                artifact_type=ArtifactType.LRAT,
                tool_name="test",
                parent_hashes=[meta_a.artifact_hash],
                copy_to_store=False,
            )
            
            file_c = Path(tmpdir) / "c.txt"
            file_c.write_text("C")
            meta_c = store.register(
                file_path=file_c,
                artifact_type=ArtifactType.LEAN_PROOF,
                tool_name="test",
                parent_hashes=[meta_b.artifact_hash],
                copy_to_store=False,
            )
            
            # Get lineage of C
            print(f"[Test] Getting lineage of C")
            lineage = store.get_lineage(meta_c.artifact_hash)
            
            # Should have all three in order: A, B, C
            assert len(lineage) == 3
            assert lineage[0].artifact_hash == meta_a.artifact_hash
            assert lineage[1].artifact_hash == meta_b.artifact_hash
            assert lineage[2].artifact_hash == meta_c.artifact_hash
            
            print(f"[Test] Lineage: A -> B -> C")
    
    def test_get_children(self):
        """Test getting direct children of an artifact."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating parent with multiple children")
            
            # Register parent
            parent_file = Path(tmpdir) / "parent.txt"
            parent_file.write_text("Parent")
            parent = store.register(
                file_path=parent_file,
                artifact_type=ArtifactType.CNF,
                tool_name="test",
                copy_to_store=False,
            )
            
            # Register children
            child_hashes = []
            for i in range(3):
                child_file = Path(tmpdir) / f"child{i}.txt"
                child_file.write_text(f"Child {i}")
                child = store.register(
                    file_path=child_file,
                    artifact_type=ArtifactType.LRAT,
                    tool_name="test",
                    parent_hashes=[parent.artifact_hash],
                    copy_to_store=False,
                )
                child_hashes.append(child.artifact_hash)
            
            # Get children
            print(f"[Test] Getting children of parent")
            children = store.get_children(parent.artifact_hash)
            
            assert len(children) == 3
            for child in children:
                assert child.artifact_hash in child_hashes
                assert parent.artifact_hash in child.parent_hashes
            
            print(f"[Test] Found {len(children)} children")


class TestStoreStatistics:
    """Test store statistics."""
    
    def test_stats(self):
        """Test getting store statistics."""
        with tempfile.TemporaryDirectory() as tmpdir:
            store_dir = Path(tmpdir)
            store = ArtifactStore(store_dir)
            
            print(f"\n[Test] Creating diverse artifacts")
            
            # Register artifacts of different types and tools
            for i in range(5):
                test_file = Path(tmpdir) / f"test{i}.txt"
                test_file.write_text(f"Content {i}")
                
                artifact_type = ArtifactType.CNF if i < 3 else ArtifactType.LRAT
                tool_name = "tool_a" if i % 2 == 0 else "tool_b"
                
                store.register(
                    file_path=test_file,
                    artifact_type=artifact_type,
                    tool_name=tool_name,
                    copy_to_store=False,
                )
            
            # Get stats
            print(f"[Test] Computing statistics")
            stats = store.stats()
            
            assert stats["total_artifacts"] == 5
            assert stats["verified_count"] == 5
            assert stats["unverified_count"] == 0
            assert stats["by_type"]["cnf"] == 3
            assert stats["by_type"]["lrat"] == 2
            assert "tool_a" in stats["by_tool"]
            assert "tool_b" in stats["by_tool"]
            
            print(f"[Test] Statistics: {stats}")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])

