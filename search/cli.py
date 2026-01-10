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
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Benchmark config YAML file"),
    baseline: Optional[Path] = typer.Option(None, "--baseline", "-b", help="Baseline CSV for comparison"),
    output_dir: Optional[Path] = typer.Option(None, "--output-dir", "-o", help="Output directory"),
    fail_fast: bool = typer.Option(False, "--fail-fast", help="Stop on first failure"),
    verbose: bool = typer.Option(False, "--verbose", "-v", help="Show detailed progress"),
):
    """
    Run deterministic benchmark harness with test matrix.
    
    Executes comprehensive benchmarks across circuit types, sizes, and seeds.
    Generates CSV and Markdown reports with timing and success metrics.
    
    Examples:
        satday bench
        satday bench --config=custom_bench.yaml
        satday bench --baseline=docs/benchmarks/2026-01-10_baseline.csv
        satday bench --verbose --fail-fast
    """
    console.print("[bold blue]SATurday Benchmark Harness[/bold blue]")
    console.print()
    
    try:
        # Import benchmark modules
        from search.benchmarks.config import BenchmarkConfig
        from search.benchmarks.harness import BenchmarkHarness
        
        # Load configuration
        if config:
            console.print(f"[yellow]Loading config from {config}[/yellow]")
            bench_config = BenchmarkConfig.from_yaml(config)
        else:
            console.print("[yellow]Using default benchmark configuration[/yellow]")
            # Load default config
            default_config_path = repo_root / "infra" / "config" / "benchmark_defaults.yaml"
            if default_config_path.exists():
                bench_config = BenchmarkConfig.from_yaml(default_config_path)
            else:
                bench_config = BenchmarkConfig.default()
        
        console.print(f"Config: {bench_config.config.name}")
        console.print(f"Description: {bench_config.config.description}")
        console.print()
        
        # Set baseline if provided
        if baseline:
            console.print(f"[yellow]Baseline: {baseline}[/yellow]")
            # TODO: Implement baseline comparison in future
        
        # Initialize harness
        harness = BenchmarkHarness(
            config=bench_config,
            fail_fast=fail_fast,
            verbose=verbose,
        )
        
        # Run benchmark suite
        console.print("[bold green]Starting benchmark run...[/bold green]")
        console.print()
        
        metrics = harness.run()
        
        # Generate reports
        console.print()
        output_path = Path(output_dir) if output_dir else None
        report_paths = harness.generate_reports(output_dir=output_path)
        
        # Print summary
        console.print()
        console.print("[bold green]Benchmark Complete![/bold green]")
        console.print()
        
        # Create summary table
        table = Table(title="Summary")
        table.add_column("Metric", style="cyan")
        table.add_column("Value", style="green")
        
        table.add_row("Total Instances", str(metrics.total_instances))
        table.add_row("Successful", str(metrics.successful_instances))
        table.add_row("Failed", str(metrics.failed_instances))
        table.add_row("Success Rate", f"{metrics.success_rate:.1f}%")
        table.add_row("Duration", f"{metrics.duration:.2f}s")
        
        console.print(table)
        console.print()
        
        console.print(f"[bold]Reports:[/bold]")
        console.print(f"  CSV: {report_paths['csv']}")
        console.print(f"  Markdown: {report_paths['md']}")
        
        # Exit with error if any failures
        if metrics.failed_instances > 0:
            console.print()
            console.print(f"[bold yellow]Warning:[/bold yellow] {metrics.failed_instances} instance(s) failed")
            raise typer.Exit(code=1)
        
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        import traceback
        if verbose:
            console.print(traceback.format_exc())
        raise typer.Exit(code=1)


@app.command(name="check-proofs")
def check_proofs(
    verify_all: bool = typer.Option(False, "--all", help="Verify all stored LRAT proofs"),
    proof_hash: Optional[str] = typer.Option(None, "--hash", help="Verify specific LRAT proof by hash"),
    verbose: bool = typer.Option(False, "--verbose", "-v", help="Show detailed output"),
):
    """
    Replay LRAT verification for stored proofs.
    
    Verifies LRAT proofs against their parent CNF files using external checker.
    Ensures that solver-generated proofs are valid and have not been tampered with.
    
    Examples:
        satday check-proofs --all
        satday check-proofs --hash=abc123def456
        satday check-proofs --all --verbose
    """
    console.print("[bold blue]SATurday LRAT Proof Verification[/bold blue]")
    console.print()
    
    try:
        # Initialize artifact store
        proofs_dir = repo_root / "proofs"
        store = ArtifactStore(proofs_dir)
        
        if verify_all:
            console.print("[yellow]Verifying all LRAT proofs...[/yellow]\n")
            
            # Use new LRAT-specific verification
            summary = store.verify_all_lrat_proofs()
            
            total = summary["total_lrat_proofs"]
            verified = summary["verified"]
            failed = summary["failed"]
            results = summary["results"]
            
            if total == 0:
                console.print("[yellow]No LRAT proofs found in store[/yellow]")
                return
            
            console.print(f"Found {total} LRAT proofs")
            
            # Show details if verbose
            if verbose:
                for result in results:
                    lrat_hash = result["lrat_hash"]
                    cnf_hash = result.get("cnf_hash", "unknown")
                    success = result["success"]
                    message = result["message"]
                    
                    status_icon = "[green]✓[/green]" if success else "[red]✗[/red]"
                    console.print(f"{status_icon} LRAT: {lrat_hash[:16]}...")
                    console.print(f"     CNF:  {cnf_hash[:16] if cnf_hash else 'unknown'}...")
                    console.print(f"     {message}")
                    console.print()
            
            # Summary table
            from rich.table import Table
            table = Table(show_header=True, header_style="bold magenta")
            table.add_column("Metric", style="cyan")
            table.add_column("Count", justify="right")
            table.add_row("Total LRAT Proofs", str(total))
            table.add_row("Verified", f"[green]{verified}[/green]")
            table.add_row("Failed", f"[red]{failed}[/red]" if failed > 0 else "0")
            
            console.print(table)
            
            if failed > 0:
                console.print("\n[bold red]Some proofs failed verification![/bold red]")
                console.print("[yellow]This may indicate:[/yellow]")
                console.print("  - Proof files have been modified")
                console.print("  - CNF files are missing or corrupted")
                console.print("  - LRAT checker encountered an error")
                raise typer.Exit(code=1)
            else:
                console.print("\n[bold green]All LRAT proofs verified successfully![/bold green]")
        
        elif proof_hash:
            console.print(f"[yellow]Verifying LRAT proof: {proof_hash}[/yellow]\n")
            
            result = store.verify_lrat_proof(proof_hash)
            
            if result["success"]:
                console.print(f"[green]✓ {result['message']}[/green]")
                
                if verbose:
                    console.print("\nDetails:")
                    console.print(f"  LRAT Hash: {result['lrat_hash']}")
                    console.print(f"  CNF Hash:  {result.get('cnf_hash', 'unknown')}")
                    console.print(f"  Verified:  {result['verified_at']}")
                    
                    # Get metadata
                    metadata = store.get(proof_hash)
                    if metadata:
                        console.print(f"\nArtifact Info:")
                        console.print(f"  Type: {metadata.artifact_type.value}")
                        console.print(f"  Tool: {metadata.tool_name}")
                        console.print(f"  Created: {metadata.timestamp}")
            else:
                console.print(f"[red]✗ {result['message']}[/red]")
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

