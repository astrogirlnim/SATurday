"""
Content-addressed artifact storage system with metadata tracking.

The artifact store provides:
1. SHA256-based content addressing for all artifacts
2. Structured metadata tracking (timestamps, lineage, tool versions)
3. Query interface for finding artifacts by properties
4. Integrity validation via hash verification

All artifacts are stored in the proofs/ directory with SHA256 filenames.
Metadata is maintained in proofs/index.json with fast lookup.
"""

import hashlib
import json
import sys
import time
from dataclasses import dataclass, field, asdict
from enum import Enum
from pathlib import Path
from typing import Dict, List, Optional, Any, Set


class ArtifactType(Enum):
    """Types of artifacts in the store."""
    CNF = "cnf"                    # DIMACS CNF file
    LRAT = "lrat"                  # LRAT unsatisfiability proof
    SOLVER_LOG = "solver_log"      # SAT solver output log
    LEAN_PROOF = "lean_proof"      # Lean 4 theorem proof
    CIRCUIT = "circuit"            # Circuit specification
    PLAN = "plan"                  # Agent execution plan
    REPORT = "report"              # Markdown report
    METADATA = "metadata"          # JSON metadata file


@dataclass
class ArtifactMetadata:
    """
    Metadata for a single artifact.
    
    Attributes:
        artifact_hash: SHA256 hash of the artifact content
        artifact_type: Type of artifact (CNF, LRAT, etc.)
        file_path: Path to the artifact file
        timestamp: Creation timestamp (ISO 8601 format)
        tool_name: Name of tool that created the artifact
        tool_version: Version of the creating tool
        parent_hashes: Hashes of parent artifacts (lineage)
        properties: Additional type-specific properties
        verified: Whether artifact integrity has been verified
    """
    artifact_hash: str
    artifact_type: ArtifactType
    file_path: str
    timestamp: str
    tool_name: str
    tool_version: str = "unknown"
    parent_hashes: List[str] = field(default_factory=list)
    properties: Dict[str, Any] = field(default_factory=dict)
    verified: bool = False
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        result = asdict(self)
        result["artifact_type"] = self.artifact_type.value
        return result
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "ArtifactMetadata":
        """Create metadata from dictionary."""
        # Convert artifact_type string back to enum
        if isinstance(data["artifact_type"], str):
            data["artifact_type"] = ArtifactType(data["artifact_type"])
        return cls(**data)


class ArtifactStore:
    """
    Content-addressed artifact storage with metadata tracking.
    
    Provides registration, querying, and validation of artifacts.
    All artifacts are stored with SHA256 filenames for determinism.
    """
    
    def __init__(self, store_dir: Path):
        """
        Initialize artifact store.
        
        Args:
            store_dir: Directory for artifact storage (typically proofs/)
        """
        self.store_dir = Path(store_dir)
        self.index_path = self.store_dir / "index.json"
        self.index: Dict[str, ArtifactMetadata] = {}
        
        # Create store directory if needed
        self.store_dir.mkdir(parents=True, exist_ok=True)
        
        # Load existing index
        self._load_index()
        
        print(f"[ArtifactStore] Initialized at {self.store_dir}", file=sys.stderr)
        print(f"[ArtifactStore] Loaded {len(self.index)} artifacts from index", file=sys.stderr)
    
    def _load_index(self) -> None:
        """Load index from disk."""
        if not self.index_path.exists():
            print(f"[ArtifactStore] No existing index at {self.index_path}, starting fresh", file=sys.stderr)
            self.index = {}
            return
        
        print(f"[ArtifactStore] Loading index from {self.index_path}", file=sys.stderr)
        
        try:
            with open(self.index_path, "r") as f:
                data = json.load(f)
            
            # Convert to ArtifactMetadata objects
            self.index = {
                hash_key: ArtifactMetadata.from_dict(meta_dict)
                for hash_key, meta_dict in data.items()
            }
            
            print(f"[ArtifactStore] Loaded {len(self.index)} artifacts", file=sys.stderr)
            
        except Exception as e:
            print(f"[ArtifactStore] WARNING: Failed to load index: {e}", file=sys.stderr)
            print(f"[ArtifactStore] Starting with empty index", file=sys.stderr)
            self.index = {}
    
    def _save_index(self) -> None:
        """Save index to disk."""
        print(f"[ArtifactStore] Saving index with {len(self.index)} artifacts", file=sys.stderr)
        
        # Convert to dictionaries for JSON serialization
        data = {
            hash_key: meta.to_dict()
            for hash_key, meta in self.index.items()
        }
        
        # Write atomically via temp file
        temp_path = self.index_path.with_suffix(".json.tmp")
        
        try:
            with open(temp_path, "w") as f:
                json.dump(data, f, indent=2)
            
            # Atomic rename
            temp_path.replace(self.index_path)
            
            print(f"[ArtifactStore] Index saved to {self.index_path}", file=sys.stderr)
            
        except Exception as e:
            print(f"[ArtifactStore] ERROR: Failed to save index: {e}", file=sys.stderr)
            if temp_path.exists():
                temp_path.unlink()
            raise
    
    def compute_hash(self, file_path: Path) -> str:
        """
        Compute SHA256 hash of a file.
        
        Args:
            file_path: Path to file
            
        Returns:
            Hexadecimal SHA256 hash string
        """
        print(f"[ArtifactStore] Computing SHA256 for {file_path}", file=sys.stderr)
        
        sha256 = hashlib.sha256()
        
        with open(file_path, "rb") as f:
            # Read in chunks for memory efficiency
            for chunk in iter(lambda: f.read(4096), b""):
                sha256.update(chunk)
        
        hash_value = sha256.hexdigest()
        print(f"[ArtifactStore] SHA256: {hash_value}", file=sys.stderr)
        
        return hash_value
    
    def register(
        self,
        file_path: Path,
        artifact_type: ArtifactType,
        tool_name: str,
        tool_version: str = "unknown",
        parent_hashes: Optional[List[str]] = None,
        properties: Optional[Dict[str, Any]] = None,
        copy_to_store: bool = True,
    ) -> ArtifactMetadata:
        """
        Register an artifact in the store.
        
        Args:
            file_path: Path to artifact file
            artifact_type: Type of artifact
            tool_name: Name of tool that created artifact
            tool_version: Version of creating tool
            parent_hashes: List of parent artifact hashes (lineage)
            properties: Additional metadata properties
            copy_to_store: Whether to copy file to store (default True)
            
        Returns:
            ArtifactMetadata for registered artifact
            
        Raises:
            FileNotFoundError: If file_path doesn't exist
        """
        if not file_path.exists():
            raise FileNotFoundError(f"Artifact file not found: {file_path}", file=sys.stderr)
        
        print(f"[ArtifactStore] Registering artifact: {file_path}", file=sys.stderr)
        print(f"[ArtifactStore]   Type: {artifact_type.value}", file=sys.stderr)
        print(f"[ArtifactStore]   Tool: {tool_name} v{tool_version}", file=sys.stderr)
        
        # Compute hash
        artifact_hash = self.compute_hash(file_path)
        
        # Check if already registered
        if artifact_hash in self.index:
            print(f"[ArtifactStore] Artifact already registered: {artifact_hash}", file=sys.stderr)
            existing = self.index[artifact_hash]
            print(f"[ArtifactStore]   Existing file: {existing.file_path}", file=sys.stderr)
            return existing
        
        # Copy to store if requested
        if copy_to_store:
            # Determine target filename based on type
            suffix = file_path.suffix or self._get_default_suffix(artifact_type)
            target_name = f"{artifact_hash}{suffix}"
            target_path = self.store_dir / target_name
            
            if not target_path.exists():
                print(f"[ArtifactStore] Copying to store: {target_path}", file=sys.stderr)
                target_path.write_bytes(file_path.read_bytes())
            else:
                print(f"[ArtifactStore] File already in store: {target_path}", file=sys.stderr)
            
            final_path = str(target_path)
        else:
            final_path = str(file_path.resolve())
        
        # Create metadata
        metadata = ArtifactMetadata(
            artifact_hash=artifact_hash,
            artifact_type=artifact_type,
            file_path=final_path,
            timestamp=time.strftime("%Y-%m-%d %H:%M:%S"),
            tool_name=tool_name,
            tool_version=tool_version,
            parent_hashes=parent_hashes or [],
            properties=properties or {},
            verified=True,  # Just computed hash, so verified
        )
        
        # Add to index
        self.index[artifact_hash] = metadata
        
        # Log lineage
        if metadata.parent_hashes:
            print(f"[ArtifactStore] Lineage: {len(metadata.parent_hashes)} parent(s)", file=sys.stderr)
            for parent_hash in metadata.parent_hashes[:3]:  # Show first 3
                print(f"[ArtifactStore]   Parent: {parent_hash[:16]}...", file=sys.stderr)
        
        # Save index
        self._save_index()
        
        print(f"[ArtifactStore] Registered: {artifact_hash}", file=sys.stderr)
        
        return metadata
    
    def _get_default_suffix(self, artifact_type: ArtifactType) -> str:
        """Get default file suffix for artifact type."""
        suffix_map = {
            ArtifactType.CNF: ".cnf",
            ArtifactType.LRAT: ".lrat",
            ArtifactType.SOLVER_LOG: ".log",
            ArtifactType.LEAN_PROOF: ".lean",
            ArtifactType.CIRCUIT: ".json",
            ArtifactType.PLAN: ".yaml",
            ArtifactType.REPORT: ".md",
            ArtifactType.METADATA: ".json",
        }
        return suffix_map.get(artifact_type, ".dat", file=sys.stderr)
    
    def get(self, artifact_hash: str) -> Optional[ArtifactMetadata]:
        """
        Get metadata for an artifact by hash.
        
        Args:
            artifact_hash: SHA256 hash of artifact
            
        Returns:
            ArtifactMetadata if found, None otherwise
        """
        return self.index.get(artifact_hash)
    
    def query(
        self,
        artifact_type: Optional[ArtifactType] = None,
        tool_name: Optional[str] = None,
        parent_hash: Optional[str] = None,
        properties: Optional[Dict[str, Any]] = None,
    ) -> List[ArtifactMetadata]:
        """
        Query artifacts by properties.
        
        Args:
            artifact_type: Filter by artifact type
            tool_name: Filter by creating tool name
            parent_hash: Filter by parent hash (artifacts derived from this)
            properties: Filter by custom properties (exact match)
            
        Returns:
            List of matching ArtifactMetadata objects
        """
        print(f"[ArtifactStore] Querying artifacts:", file=sys.stderr)
        if artifact_type:
            print(f"[ArtifactStore]   Type: {artifact_type.value}", file=sys.stderr)
        if tool_name:
            print(f"[ArtifactStore]   Tool: {tool_name}", file=sys.stderr)
        if parent_hash:
            print(f"[ArtifactStore]   Parent: {parent_hash[:16]}...", file=sys.stderr)
        if properties:
            print(f"[ArtifactStore]   Properties: {properties}", file=sys.stderr)
        
        results = []
        
        for metadata in self.index.values():
            # Check filters
            if artifact_type and metadata.artifact_type != artifact_type:
                continue
            
            if tool_name and metadata.tool_name != tool_name:
                continue
            
            if parent_hash and parent_hash not in metadata.parent_hashes:
                continue
            
            if properties:
                # Check all property filters match
                match = all(
                    metadata.properties.get(k) == v
                    for k, v in properties.items()
                )
                if not match:
                    continue
            
            results.append(metadata)
        
        print(f"[ArtifactStore] Found {len(results)} matching artifacts", file=sys.stderr)
        
        return results
    
    def verify(self, artifact_hash: str) -> bool:
        """
        Verify artifact integrity by recomputing hash.
        
        Args:
            artifact_hash: Hash of artifact to verify
            
        Returns:
            True if hash matches, False otherwise
        """
        print(f"[ArtifactStore] Verifying artifact: {artifact_hash[:16]}...", file=sys.stderr)
        
        metadata = self.get(artifact_hash)
        if not metadata:
            print(f"[ArtifactStore] ERROR: Artifact not in index", file=sys.stderr)
            return False
        
        file_path = Path(metadata.file_path)
        if not file_path.exists():
            print(f"[ArtifactStore] ERROR: File not found: {file_path}", file=sys.stderr)
            return False
        
        # Recompute hash
        computed_hash = self.compute_hash(file_path)
        
        if computed_hash == artifact_hash:
            print(f"[ArtifactStore] Verification SUCCESS", file=sys.stderr)
            metadata.verified = True
            self._save_index()
            return True
        else:
            print(f"[ArtifactStore] Verification FAILED", file=sys.stderr)
            print(f"[ArtifactStore]   Expected: {artifact_hash}", file=sys.stderr)
            print(f"[ArtifactStore]   Computed: {computed_hash}", file=sys.stderr)
            metadata.verified = False
            self._save_index()
            return False
    
    def verify_all(self) -> Dict[str, bool]:
        """
        Verify all artifacts in the store.
        
        Returns:
            Dictionary mapping artifact_hash to verification result
        """
        print(f"[ArtifactStore] Verifying all {len(self.index)} artifacts", file=sys.stderr)
        
        results = {}
        
        for artifact_hash in self.index.keys():
            results[artifact_hash] = self.verify(artifact_hash)
        
        success_count = sum(1 for v in results.values() if v)
        print(f"[ArtifactStore] Verification complete: {success_count}/{len(results)} passed", file=sys.stderr)
        
        return results
    
    def get_lineage(self, artifact_hash: str) -> List[ArtifactMetadata]:
        """
        Get full lineage (ancestors) of an artifact.
        
        Args:
            artifact_hash: Hash of artifact
            
        Returns:
            List of ancestor ArtifactMetadata in topological order
        """
        print(f"[ArtifactStore] Tracing lineage for: {artifact_hash[:16]}...", file=sys.stderr)
        
        lineage = []
        visited: Set[str] = set()
        
        def _trace(hash_val: str) -> None:
            """Recursively trace lineage."""
            if hash_val in visited:
                return
            
            visited.add(hash_val)
            
            metadata = self.get(hash_val)
            if not metadata:
                return
            
            # Trace parents first (depth-first)
            for parent_hash in metadata.parent_hashes:
                _trace(parent_hash)
            
            lineage.append(metadata)
        
        _trace(artifact_hash)
        
        print(f"[ArtifactStore] Lineage depth: {len(lineage)}", file=sys.stderr)
        
        return lineage
    
    def get_children(self, artifact_hash: str) -> List[ArtifactMetadata]:
        """
        Get direct children (artifacts derived from this one).
        
        Args:
            artifact_hash: Hash of parent artifact
            
        Returns:
            List of child ArtifactMetadata
        """
        print(f"[ArtifactStore] Finding children of: {artifact_hash[:16]}...", file=sys.stderr)
        
        children = [
            metadata
            for metadata in self.index.values()
            if artifact_hash in metadata.parent_hashes
        ]
        
        print(f"[ArtifactStore] Found {len(children)} children", file=sys.stderr)
        
        return children
    
    def verify_lrat_proof(self, lrat_hash: str) -> Dict[str, Any]:
        """
        Verify an LRAT proof against its parent CNF.
        
        Args:
            lrat_hash: Hash of LRAT proof artifact
            
        Returns:
            Dictionary with verification result:
                - success: bool
                - message: str
                - lrat_hash: str
                - cnf_hash: Optional[str]
                - verified_at: str (timestamp)
        """
        print(f"[ArtifactStore] Verifying LRAT proof: {lrat_hash[:16]}...", file=sys.stderr)
        
        # Get LRAT metadata
        lrat_metadata = self.get(lrat_hash)
        if not lrat_metadata:
            return {
                "success": False,
                "message": f"LRAT proof not in index: {lrat_hash}",
                "lrat_hash": lrat_hash,
                "cnf_hash": None,
                "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
        
        # Check LRAT file exists
        lrat_path = Path(lrat_metadata.file_path)
        if not lrat_path.exists():
            return {
                "success": False,
                "message": f"LRAT file not found: {lrat_path}",
                "lrat_hash": lrat_hash,
                "cnf_hash": None,
                "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
        
        # Find parent CNF
        cnf_hash = None
        cnf_path = None
        
        for parent_hash in lrat_metadata.parent_hashes:
            parent_metadata = self.get(parent_hash)
            if parent_metadata and parent_metadata.artifact_type == ArtifactType.CNF:
                cnf_hash = parent_hash
                cnf_path = Path(parent_metadata.file_path)
                break
        
        if not cnf_path:
            return {
                "success": False,
                "message": "No parent CNF found for LRAT proof",
                "lrat_hash": lrat_hash,
                "cnf_hash": cnf_hash,
                "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
        
        # Call external LRAT verifier
        import subprocess
        from pathlib import Path as PathType
        
        verifier_path = Path(__file__).parent.parent / "bin" / "verify_lrat"
        
        try:
            result = subprocess.run(
                ["python", str(verifier_path), "--cnf", str(cnf_path), "--lrat", str(lrat_path)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            
            success = result.returncode == 0
            message = result.stdout.strip() if success else result.stderr.strip()
            
            # Update metadata if successful
            if success:
                lrat_metadata.verified = True
                lrat_metadata.properties["lrat_verified_at"] = time.strftime("%Y-%m-%dT%H:%M:%S")
                self._save_index()
            
            return {
                "success": success,
                "message": message,
                "lrat_hash": lrat_hash,
                "cnf_hash": cnf_hash,
                "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
            
        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "message": "LRAT verification timeout (30s)",
                "lrat_hash": lrat_hash,
                "cnf_hash": cnf_hash,
                "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
        except Exception as e:
            return {
                "success": False,
                "message": f"LRAT verification error: {e}",
                "lrat_hash": lrat_hash,
                "cnf_hash": cnf_hash,
                "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
    
    def verify_all_lrat_proofs(self) -> Dict[str, Any]:
        """
        Verify all LRAT proofs in the store.
        
        Returns:
            Dictionary with verification summary:
                - total_lrat_proofs: int
                - verified: int
                - failed: int
                - results: List[Dict] - individual results
        """
        print(f"[ArtifactStore] Verifying all LRAT proofs", file=sys.stderr)
        
        # Find all LRAT artifacts
        lrat_artifacts = self.query(artifact_type=ArtifactType.LRAT)
        
        print(f"[ArtifactStore] Found {len(lrat_artifacts)} LRAT proofs", file=sys.stderr)
        
        results = []
        verified_count = 0
        failed_count = 0
        
        for lrat_metadata in lrat_artifacts:
            result = self.verify_lrat_proof(lrat_metadata.artifact_hash)
            results.append(result)
            
            if result["success"]:
                verified_count += 1
            else:
                failed_count += 1
        
        summary = {
            "total_lrat_proofs": len(lrat_artifacts),
            "verified": verified_count,
            "failed": failed_count,
            "results": results,
        }
        
        print(f"[ArtifactStore] LRAT verification complete: {verified_count}/{len(lrat_artifacts)} passed", 
              file=sys.stderr)
        
        return summary
    
    def stats(self) -> Dict[str, Any]:
        """
        Get statistics about the artifact store.
        
        Returns:
            Dictionary with store statistics
        """
        print(f"[ArtifactStore] Computing statistics", file=sys.stderr)
        
        stats_data = {
            "total_artifacts": len(self.index),
            "by_type": {},
            "by_tool": {},
            "verified_count": 0,
            "unverified_count": 0,
            "total_size_bytes": 0,
        }
        
        for metadata in self.index.values():
            # Count by type
            type_key = metadata.artifact_type.value
            stats_data["by_type"][type_key] = stats_data["by_type"].get(type_key, 0) + 1
            
            # Count by tool
            tool_key = metadata.tool_name
            stats_data["by_tool"][tool_key] = stats_data["by_tool"].get(tool_key, 0) + 1
            
            # Verification status
            if metadata.verified:
                stats_data["verified_count"] += 1
            else:
                stats_data["unverified_count"] += 1
            
            # File size
            file_path = Path(metadata.file_path)
            if file_path.exists():
                stats_data["total_size_bytes"] += file_path.stat().st_size
        
        print(f"[ArtifactStore] Statistics: {stats_data['total_artifacts']} artifacts", file=sys.stderr)
        
        return stats_data

