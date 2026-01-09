#!/usr/bin/env python3
"""
CLI tool for inspecting and querying the artifact store.

This tool provides commands for:
1. Listing all artifacts in the store
2. Showing details of a specific artifact
3. Displaying lineage graphs
4. Verifying artifact integrity
5. Getting store statistics

Usage:
    inspect_artifacts.py list [--type TYPE] [--tool TOOL]
    inspect_artifacts.py show <HASH>
    inspect_artifacts.py lineage <HASH>
    inspect_artifacts.py children <HASH>
    inspect_artifacts.py verify [HASH]
    inspect_artifacts.py stats
"""

import argparse
import sys
from pathlib import Path
from typing import Optional

# Add parent to path for imports
parent_dir = Path(__file__).parent.parent.parent
if str(parent_dir) not in sys.path:
    sys.path.insert(0, str(parent_dir))

from search.tools.artifact_store import ArtifactStore, ArtifactType, ArtifactMetadata


def print_separator(char: str = "=", width: int = 80) -> None:
    """Print a separator line."""
    print(char * width)


def print_artifact(metadata: ArtifactMetadata, verbose: bool = False) -> None:
    """
    Print artifact metadata in human-readable format.
    
    Args:
        metadata: Artifact metadata to print
        verbose: Whether to show all details
    """
    print(f"\nArtifact: {metadata.artifact_hash}")
    print(f"  Type: {metadata.artifact_type.value}")
    print(f"  File: {metadata.file_path}")
    print(f"  Created: {metadata.timestamp}")
    print(f"  Tool: {metadata.tool_name} v{metadata.tool_version}")
    print(f"  Verified: {'Yes' if metadata.verified else 'No'}")
    
    if metadata.parent_hashes:
        print(f"  Parents: {len(metadata.parent_hashes)}")
        if verbose:
            for i, parent in enumerate(metadata.parent_hashes, 1):
                print(f"    {i}. {parent}")
    
    if metadata.properties and verbose:
        print(f"  Properties:")
        for key, value in metadata.properties.items():
            print(f"    {key}: {value}")


def cmd_list(
    store: ArtifactStore,
    artifact_type: Optional[str],
    tool_name: Optional[str],
) -> None:
    """
    List all artifacts in the store.
    
    Args:
        store: Artifact store instance
        artifact_type: Optional type filter
        tool_name: Optional tool name filter
    """
    print_separator()
    print("ARTIFACT STORE LISTING")
    print_separator()
    
    # Parse type filter
    type_filter = None
    if artifact_type:
        try:
            type_filter = ArtifactType(artifact_type)
        except ValueError:
            print(f"ERROR: Invalid artifact type '{artifact_type}'")
            print(f"Valid types: {', '.join(t.value for t in ArtifactType)}")
            sys.exit(1)
    
    # Query artifacts
    artifacts = store.query(
        artifact_type=type_filter,
        tool_name=tool_name,
    )
    
    if not artifacts:
        print("No artifacts found matching filters.")
        return
    
    # Print summary
    print(f"\nFound {len(artifacts)} artifact(s):")
    print()
    
    # Sort by timestamp (newest first)
    artifacts.sort(key=lambda m: m.timestamp, reverse=True)
    
    for metadata in artifacts:
        print_artifact(metadata, verbose=False)
    
    print_separator()


def cmd_show(store: ArtifactStore, artifact_hash: str) -> None:
    """
    Show detailed information about a specific artifact.
    
    Args:
        store: Artifact store instance
        artifact_hash: Hash of artifact to show
    """
    print_separator()
    print("ARTIFACT DETAILS")
    print_separator()
    
    metadata = store.get(artifact_hash)
    
    if not metadata:
        print(f"ERROR: Artifact not found: {artifact_hash}")
        sys.exit(1)
    
    print_artifact(metadata, verbose=True)
    
    # Show children if any
    children = store.get_children(artifact_hash)
    if children:
        print(f"\n  Children: {len(children)}")
        for i, child in enumerate(children, 1):
            print(f"    {i}. {child.artifact_hash[:16]}... ({child.artifact_type.value})")
    
    # Check file exists
    file_path = Path(metadata.file_path)
    if file_path.exists():
        size_bytes = file_path.stat().st_size
        print(f"\n  File size: {size_bytes:,} bytes")
    else:
        print(f"\n  WARNING: File not found at {metadata.file_path}")
    
    print_separator()


def cmd_lineage(store: ArtifactStore, artifact_hash: str) -> None:
    """
    Show lineage (ancestry tree) for an artifact.
    
    Args:
        store: Artifact store instance
        artifact_hash: Hash of artifact to trace
    """
    print_separator()
    print("ARTIFACT LINEAGE")
    print_separator()
    
    lineage = store.get_lineage(artifact_hash)
    
    if not lineage:
        print(f"ERROR: Artifact not found: {artifact_hash}")
        sys.exit(1)
    
    print(f"\nLineage depth: {len(lineage)} artifact(s)")
    print("\nAncestry tree (oldest first):")
    print()
    
    # Print lineage with indentation based on depth
    for i, metadata in enumerate(lineage):
        indent = "  " * i
        marker = "└─" if i > 0 else "  "
        
        print(f"{indent}{marker} {metadata.artifact_hash[:16]}...")
        print(f"{indent}   Type: {metadata.artifact_type.value}")
        print(f"{indent}   Tool: {metadata.tool_name}")
        print(f"{indent}   Time: {metadata.timestamp}")
        print()
    
    print_separator()


def cmd_children(store: ArtifactStore, artifact_hash: str) -> None:
    """
    Show direct children (derived artifacts) for an artifact.
    
    Args:
        store: Artifact store instance
        artifact_hash: Hash of parent artifact
    """
    print_separator()
    print("DERIVED ARTIFACTS (CHILDREN)")
    print_separator()
    
    metadata = store.get(artifact_hash)
    if not metadata:
        print(f"ERROR: Artifact not found: {artifact_hash}")
        sys.exit(1)
    
    children = store.get_children(artifact_hash)
    
    print(f"\nParent: {artifact_hash}")
    print(f"  Type: {metadata.artifact_type.value}")
    print(f"  File: {metadata.file_path}")
    print(f"\nChildren: {len(children)}")
    print()
    
    if not children:
        print("No derived artifacts found.")
    else:
        for child in children:
            print_artifact(child, verbose=False)
    
    print_separator()


def cmd_verify(store: ArtifactStore, artifact_hash: Optional[str]) -> None:
    """
    Verify artifact integrity by recomputing hashes.
    
    Args:
        store: Artifact store instance
        artifact_hash: Optional specific artifact to verify (None = verify all)
    """
    print_separator()
    print("ARTIFACT VERIFICATION")
    print_separator()
    
    if artifact_hash:
        # Verify single artifact
        print(f"\nVerifying: {artifact_hash}")
        
        metadata = store.get(artifact_hash)
        if not metadata:
            print(f"ERROR: Artifact not found")
            sys.exit(1)
        
        success = store.verify(artifact_hash)
        
        if success:
            print("\nResult: VERIFICATION PASSED")
            print(f"  File: {metadata.file_path}")
            print(f"  Hash: {artifact_hash}")
        else:
            print("\nResult: VERIFICATION FAILED")
            print(f"  File integrity compromised or file missing")
            sys.exit(1)
    
    else:
        # Verify all artifacts
        print(f"\nVerifying all artifacts in store...")
        
        results = store.verify_all()
        
        passed = sum(1 for v in results.values() if v)
        failed = len(results) - passed
        
        print(f"\nVerification complete:")
        print(f"  Total: {len(results)}")
        print(f"  Passed: {passed}")
        print(f"  Failed: {failed}")
        
        if failed > 0:
            print(f"\nFailed artifacts:")
            for hash_val, success in results.items():
                if not success:
                    print(f"  - {hash_val}")
            sys.exit(1)
    
    print_separator()


def cmd_stats(store: ArtifactStore) -> None:
    """
    Show statistics about the artifact store.
    
    Args:
        store: Artifact store instance
    """
    print_separator()
    print("ARTIFACT STORE STATISTICS")
    print_separator()
    
    stats = store.stats()
    
    print(f"\nTotal artifacts: {stats['total_artifacts']}")
    print(f"Verified: {stats['verified_count']}")
    print(f"Unverified: {stats['unverified_count']}")
    print(f"Total size: {stats['total_size_bytes']:,} bytes")
    
    print(f"\nBy type:")
    for artifact_type, count in sorted(stats['by_type'].items()):
        print(f"  {artifact_type}: {count}")
    
    print(f"\nBy tool:")
    for tool_name, count in sorted(stats['by_tool'].items()):
        print(f"  {tool_name}: {count}")
    
    print_separator()


def main() -> None:
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Inspect and query the artifact store",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    
    parser.add_argument(
        "--store-dir",
        type=Path,
        default=None,
        help="Artifact store directory (default: proofs/)",
    )
    
    subparsers = parser.add_subparsers(dest="command", help="Command to run")
    
    # list command
    list_parser = subparsers.add_parser("list", help="List artifacts")
    list_parser.add_argument("--type", help="Filter by artifact type")
    list_parser.add_argument("--tool", help="Filter by tool name")
    
    # show command
    show_parser = subparsers.add_parser("show", help="Show artifact details")
    show_parser.add_argument("hash", help="Artifact hash")
    
    # lineage command
    lineage_parser = subparsers.add_parser("lineage", help="Show artifact lineage")
    lineage_parser.add_argument("hash", help="Artifact hash")
    
    # children command
    children_parser = subparsers.add_parser("children", help="Show derived artifacts")
    children_parser.add_argument("hash", help="Parent artifact hash")
    
    # verify command
    verify_parser = subparsers.add_parser("verify", help="Verify artifact integrity")
    verify_parser.add_argument("hash", nargs="?", help="Artifact hash (optional, verifies all if omitted)")
    
    # stats command
    stats_parser = subparsers.add_parser("stats", help="Show store statistics")
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        sys.exit(1)
    
    # Determine store directory
    if args.store_dir:
        store_dir = args.store_dir
    else:
        # Default to proofs/ relative to script location
        script_dir = Path(__file__).parent.resolve()
        store_dir = script_dir.parent.parent / "proofs"
    
    # Initialize store
    store = ArtifactStore(store_dir)
    
    # Execute command
    if args.command == "list":
        cmd_list(store, args.type, args.tool)
    elif args.command == "show":
        cmd_show(store, args.hash)
    elif args.command == "lineage":
        cmd_lineage(store, args.hash)
    elif args.command == "children":
        cmd_children(store, args.hash)
    elif args.command == "verify":
        cmd_verify(store, args.hash)
    elif args.command == "stats":
        cmd_stats(store)
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()

