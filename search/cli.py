"""
SATurday CLI - Unified command-line interface for agent-driven research.

Commands:
- mine: Run full research cycle
- bench: Benchmark deterministic harness
- check-proofs: Replay LRAT verification
- verify: Build Lean project
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Optional

import typer
from rich.console import Console
from rich.table import Table

# Add project root to path
repo_root = Path(__file__).parent.parent
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

from search.agents.supervisor import Supervisor
from search.reporting.md_reporter import MarkdownReporter
from search.tools.artifact_store import ArtifactStore

# Initialize Typer app
app = typer.Typer(
    name="satday",
    help="SATurday: Agent-Driven Research Loop for P vs NP Exploration",
    no_args_is_help=True,
)

# Initialize Rich console for pretty output
console = Console()


@app.command()
def mine(
    bet: str = typer.Option("A", "--bet", "-b", help="Research bet (A/B/C/D)"),
    n: int = typer.Option(10, "--n", "-n", help="Circuit size parameter"),
    seed: int = typer.Option(42, "--seed", "-s", help="Random seed for determinism"),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
    plan: Optional[Path] = typer.Option(None, "--plan", "-p", help="YAML plan file"),
    offline: bool = typer.Option(True, "--offline/--online", help="Enforce offline mode"),
    report: bool = typer.Option(True, "--report/--no-report", help="Generate Markdown report"),
):
    """
    Run full research cycle: conjecture generation, mining, proof, critique.
    
    This command orchestrates all agents to execute a complete research iteration.
    Results are logged to JSONL and optionally summarized in Markdown reports.
    
    Examples:
        satday mine --bet=A --n=10 --seed=42
        satday mine --plan=search/plans/bet_a.yaml
        satday mine --config=custom_config.yaml --offline
    """
    console.print(f"[bold blue]SATurday Research Miner[/bold blue]")
    console.print(f"Bet: {bet}, n={n}, seed={seed}")
    console.print(f"Offline: {offline}")
    console.print()
    
    try:
        # Log configuration
        console.print("[yellow]Initializing supervisor...[/yellow]")
        
        # Create supervisor with config
        supervisor = Supervisor(config_file=config)
        
        # Override offline mode if specified
        if offline:
            supervisor.offline = True
            supervisor.config.offline.enabled = True
        
        # Log agent count
        console.print(f"[green]Loaded {len(supervisor.agents)} agents[/green]")
        
        # Execute pipeline
        console.print("\n[yellow]Starting agent pipeline...[/yellow]\n")
        
        if plan:
            # Run from plan file
            summary = supervisor.run_from_plan_file(plan)
        else:
            # Create minimal plan from CLI params
            simple_plan = {
                "bet": bet,
                "n": n,
            }
            summary = supervisor.execute_pipeline(plan=simple_plan, seed=seed)
        
        # Print summary
        console.print("\n[bold green]Pipeline Complete![/bold green]\n")
        
        # Create summary table
        table = Table(title="Execution Summary")
        table.add_column("Agent", style="cyan")
        table.add_column("Status", style="magenta")
        table.add_column("Duration (s)", style="green")
        
        for agent_name, agent_data in summary.get("agents", {}).items():
            table.add_row(
                agent_name,
                agent_data["status"],
                f"{agent_data['duration']:.3f}",
            )
        
        console.print(table)
        console.print(f"\nRun ID: {summary['run_id']}")
        console.print(f"Total Time: {summary['total_time_seconds']:.3f}s")
        console.print(f"Log File: {summary['log_file']}")
        
        # Generate Markdown report if requested
        if report:
            console.print("\n[yellow]Generating Markdown report...[/yellow]")
            reporter = MarkdownReporter()
            report_path = reporter.generate_report(summary)
            console.print(f"[green]Report saved: {report_path}[/green]")
        
        console.print("\n[bold green]Done![/bold green]")
        
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command()
def bench(
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
    seed_start: int = typer.Option(1, "--seed-start", help="Starting seed value"),
    seed_count: int = typer.Option(10, "--seed-count", help="Number of seeds to test"),
    output: Optional[Path] = typer.Option(None, "--output", "-o", help="Output CSV file"),
):
    """
    Run deterministic benchmark harness with seed matrix.
    
    Tests small CNF instances across multiple seeds and generates CSV/MD summaries
    with timing and resource usage statistics.
    
    Examples:
        satday bench --seed-start=1 --seed-count=10
        satday bench --output=results.csv
    """
    console.print("[bold blue]SATurday Benchmark Harness[/bold blue]")
    console.print(f"Seeds: {seed_start} to {seed_start + seed_count - 1}")
    console.print()
    
    try:
        # Import benchmark module (to be implemented in R11)
        console.print("[yellow]Benchmark harness not yet implemented (Phase 3: R11)[/yellow]")
        console.print("This will run deterministic seed matrix benchmarks.")
        console.print(f"Planned output: {output or 'docs/reports/bench_TIMESTAMP.md'}")
        
        # Placeholder for future implementation
        console.print("\n[bold yellow]Coming in Phase 3![/bold yellow]")
        
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command(name="check-proofs")
def check_proofs(
    verify_all: bool = typer.Option(False, "--all", help="Verify all stored proofs"),
    proof_hash: Optional[str] = typer.Option(None, "--hash", help="Verify specific proof by hash"),
    verbose: bool = typer.Option(False, "--verbose", "-v", help="Show detailed output"),
):
    """
    Replay LRAT verification for stored proofs.
    
    Recomputes hashes and verifies integrity of all artifacts in the proof store.
    Ensures that solver-generated proofs are valid and have not been tampered with.
    
    Examples:
        satday check-proofs --all
        satday check-proofs --hash=abc123def456
    """
    console.print("[bold blue]SATurday Proof Verification[/bold blue]")
    console.print()
    
    try:
        # Initialize artifact store
        proofs_dir = repo_root / "proofs"
        store = ArtifactStore(proofs_dir)
        
        if verify_all:
            console.print("[yellow]Verifying all stored proofs...[/yellow]\n")
            
            # Get all artifacts (we'll filter LRAT)
            # Use verify_all method which returns a dict of hash -> bool
            verification_results = store.verify_all()
            
            if not verification_results:
                console.print("[yellow]No artifacts found in store[/yellow]")
                return
            
            # Filter for LRAT proofs
            from search.tools.artifact_store import ArtifactType
            lrat_results = {
                h: v for h, v in verification_results.items()
                if store.get(h) and store.get(h).artifact_type == ArtifactType.LRAT
            }
            
            if not lrat_results:
                console.print("[yellow]No LRAT proofs found in store[/yellow]")
                console.print(f"Total artifacts: {len(verification_results)}")
                return
            
            console.print(f"Found {len(lrat_results)} LRAT proofs")
            
            # Count results
            passed = sum(1 for v in lrat_results.values() if v)
            failed = sum(1 for v in lrat_results.values() if not v)
            
            # Show details if verbose
            if verbose:
                for artifact_hash, is_valid in lrat_results.items():
                    metadata = store.get(artifact_hash)
                    if metadata:
                        status_icon = "[green]✓[/green]" if is_valid else "[red]✗[/red]"
                        console.print(f"{status_icon} {artifact_hash[:16]}... {metadata.artifact_type.value}")
            
            # Summary
            console.print(f"\n[bold]Results:[/bold]")
            console.print(f"  [green]Passed: {passed}[/green]")
            console.print(f"  [red]Failed: {failed}[/red]")
            
            if failed > 0:
                console.print("\n[bold red]Some proofs failed verification![/bold red]")
                raise typer.Exit(code=1)
            else:
                console.print("\n[bold green]All proofs verified successfully![/bold green]")
        
        elif proof_hash:
            console.print(f"[yellow]Verifying proof: {proof_hash}[/yellow]\n")
            
            is_valid = store.verify(proof_hash)
            
            if is_valid:
                console.print(f"[green]✓ Proof is valid[/green]")
                
                if verbose:
                    metadata = store.get(proof_hash)
                    if metadata:
                        console.print("\nMetadata:")
                        console.print(json.dumps(metadata.to_dict(), indent=2))
            else:
                console.print(f"[red]✗ Proof verification failed[/red]")
                raise typer.Exit(code=1)
        
        else:
            console.print("[yellow]Please specify --all or --hash[/yellow]")
            raise typer.Exit(code=1)
    
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command()
def verify():
    """
    Build Lean project and verify all formal proofs.
    
    Runs 'lake build' to compile the Lean theory project and type-check all theorems.
    This ensures all formal proofs are valid and compile without errors.
    
    Examples:
        satday verify
    """
    console.print("[bold blue]SATurday Formal Verification[/bold blue]")
    console.print()
    
    try:
        theory_dir = repo_root / "theory"
        
        if not theory_dir.exists():
            console.print("[red]Error: theory/ directory not found[/red]")
            raise typer.Exit(code=1)
        
        console.print("[yellow]Running lake build...[/yellow]\n")
        
        # Run lake build
        result = subprocess.run(
            ["lake", "build"],
            cwd=theory_dir,
            capture_output=True,
            text=True,
        )
        
        # Print output
        if result.stdout:
            console.print(result.stdout)
        
        if result.returncode == 0:
            console.print("\n[bold green]All Lean proofs verified successfully![/bold green]")
        else:
            console.print("\n[bold red]Lean verification failed![/bold red]")
            if result.stderr:
                console.print(result.stderr)
            raise typer.Exit(code=1)
    
    except FileNotFoundError:
        console.print("[red]Error: 'lake' command not found. Is Lean installed?[/red]")
        raise typer.Exit(code=1)
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command()
def info():
    """
    Show system information and configuration status.
    
    Displays current configuration, enabled agents, artifact store stats,
    and system status for debugging and verification.
    """
    console.print("[bold blue]SATurday System Information[/bold blue]\n")
    
    try:
        # Show configuration
        supervisor = Supervisor()
        
        console.print("[bold]Configuration:[/bold]")
        console.print(f"  Offline Mode: {supervisor.offline}")
        console.print(f"  Cost Guard: {supervisor.config.cost.enabled}")
        console.print(f"  Max Spend: ${supervisor.config.cost.max_monthly_spend}")
        console.print(f"  Log Directory: {supervisor.log_dir}")
        
        # Show enabled agents
        console.print(f"\n[bold]Enabled Agents ({len(supervisor.agents)}):[/bold]")
        for agent in supervisor.agents:
            console.print(f"  - {agent.name}")
        
        # Show artifact store stats
        proofs_dir = repo_root / "proofs"
        if proofs_dir.exists():
            store = ArtifactStore(proofs_dir)
            stats = store.stats()
            
            console.print(f"\n[bold]Artifact Store:[/bold]")
            console.print(f"  Total Artifacts: {stats['total_artifacts']}")
            console.print(f"  CNF Files: {stats['by_type'].get('cnf', 0)}")
            console.print(f"  LRAT Proofs: {stats['by_type'].get('lrat', 0)}")
            console.print(f"  Logs: {stats['by_type'].get('log', 0)}")
        
        # Show Lean status
        theory_dir = repo_root / "theory"
        lean_toolchain = theory_dir / "lean-toolchain"
        if lean_toolchain.exists():
            version = lean_toolchain.read_text().strip()
            console.print(f"\n[bold]Lean Environment:[/bold]")
            console.print(f"  Version: {version}")
            console.print(f"  Project: {theory_dir}")
        
        console.print("\n[bold green]System ready![/bold green]")
    
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


if __name__ == "__main__":
    app()

