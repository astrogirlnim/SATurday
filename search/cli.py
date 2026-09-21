"""
SATurday CLI - Unified command-line interface for agent-driven research.

Commands:
- auto: Autonomous research loop (serial by default; --parallel for multi-rung)
- saturday: One local research cycle (CLI + localhost LLMs)
- status: Ladder completion, summit readiness, and suggested next commands
- loop: Repeated saturday wakes with optional parallel workstreams
- mine: Run legacy full research cycle
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

# Load repo .env early (OPENROUTER_API_KEY, etc.); never overwrite existing env
from infra.config.dotenv import load_dotenv

load_dotenv(repo_root)

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


@app.command("auto")
def auto_cmd(
    sleep: Optional[int] = typer.Option(
        None,
        "--sleep",
        "-s",
        help="Optional seconds between wakes (default 0: start next wake immediately)",
    ),
    cycles: int = typer.Option(
        0,
        "--cycles",
        "-n",
        help="Number of wakes (default 0 = until Ctrl-C)",
    ),
    dry_run: bool = typer.Option(False, "--dry-run", help="Plan only; no LLM calls"),
    remote: bool = typer.Option(
        False,
        "--remote",
        help="Use OpenRouter for formalize/prove; needs OPENROUTER_API_KEY",
    ),
    remote_only: bool = typer.Option(
        False,
        "--remote-only",
        help="Alias for --remote (OpenRouter formalize only)",
    ),
    escalate: bool = typer.Option(
        False,
        "--escalate",
        help="With --remote: try local first, then OpenRouter on failure",
    ),
    parallel: Optional[bool] = typer.Option(
        None,
        "--parallel/--serial",
        help=(
            "Run disjoint workstreams together each wake, or one rung at a time. "
            "Default: saturday_loop.loop_parallel_default (false = serial)."
        ),
    ),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
):
    """
    Autonomous mode: one wake after another until Ctrl-C.

    By default runs serially (one chooser pick per wake) so shared lake builds
    do not race. Pass --parallel to run R2 and R5 together when both are ready.

    Examples:
        satday auto
        satday auto --remote
        satday auto --remote --parallel
        satday auto --remote --escalate
        satday auto --sleep 30
        satday auto --cycles 5
        satday auto --dry-run --cycles 1
    """
    from infra.config.loader import load_config

    cfg = load_config(repo_root=repo_root, config_file=config)
    use_parallel = (
        bool(parallel)
        if parallel is not None
        else bool(cfg.saturday_loop.loop_parallel_default)
    )
    mode_label = "parallel" if use_parallel else "serial"
    console.print(f"[bold blue]SATurday auto ({mode_label} loop)[/bold blue]")
    if use_parallel:
        console.print(
            "Runs all next workstreams each wake, then continues immediately. "
            "Stop with Ctrl-C. Look for lines starting with >>> for human readable "
            "status; [saturday.*] lines are detailed debug logs."
        )
    else:
        console.print(
            "Runs one rung per wake (no shared-tree races), then continues "
            "immediately. Pass --parallel for R2+R5 together. Stop with Ctrl-C."
        )
    if remote_only:
        remote = True
    # Default --remote skips weak local formalize; --escalate restores local-first
    if remote and escalate:
        remote_mode = "escalate"
    elif remote or remote_only:
        remote_mode = "remote"
    else:
        remote_mode = None
    console.print(
        f"cycles={cycles} sleep={sleep} dry_run={dry_run} "
        f"parallel={use_parallel} remote={bool(remote)} remote_mode={remote_mode}"
    )
    try:
        from search.saturday.loop import run_saturday_loop

        waves = run_saturday_loop(
            repo_root=repo_root,
            config_file=config,
            cycles=cycles,
            sleep_seconds=sleep,
            parallel=use_parallel,
            dry_run=dry_run,
            remote=bool(remote),
            remote_mode=remote_mode,
        )
        console.print_json(data={"wakes": len(waves), "waves": waves})
        console.print(f"[bold green]Auto stopped wakes={len(waves)}[/bold green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command("saturday")
def saturday_cmd(
    rung: Optional[str] = typer.Option(None, "--rung", "-r", help="Rung id override"),
    action: Optional[str] = typer.Option(
        None,
        "--action",
        "-a",
        help="Action override: prove|formalize|falsify|audit",
    ),
    target: Optional[str] = typer.Option(None, "--target", "-t", help="Target override"),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
    dry_run: bool = typer.Option(False, "--dry-run", help="Choose rung/action only; no LLM"),
    parallel: bool = typer.Option(
        False,
        "--parallel",
        help="Run all disjoint workstream cycles together (typically R2 and R5)",
    ),
    remote: bool = typer.Option(
        False,
        "--remote",
        help="Use OpenRouter for formalize/prove; needs OPENROUTER_API_KEY",
    ),
    remote_only: bool = typer.Option(
        False,
        "--remote-only",
        help="Alias for --remote (OpenRouter formalize only)",
    ),
    escalate: bool = typer.Option(
        False,
        "--escalate",
        help="With --remote: try local first, then OpenRouter on failure",
    ),
):
    """
    Run exactly one local saturday cycle against the proof complexity ladder.

    With --parallel, run one cycle on each disjoint workstream (R2 and R5) in
    the same wake. Each workstream still writes its own session record.

    Examples:
        satday saturday --dry-run
        satday saturday --action prove --rung r5-cook-reckhow-bridge
        satday saturday --parallel --remote
        satday saturday --parallel --remote --escalate
        satday saturday --parallel --dry-run
    """
    console.print("[bold blue]SATurday local cycle[/bold blue]")
    if remote_only:
        remote = True
    if remote and escalate:
        remote_mode = "escalate"
    elif remote or remote_only:
        remote_mode = "remote"
    else:
        remote_mode = None
    console.print(
        f"dry_run={dry_run} parallel={parallel} rung={rung} action={action} "
        f"remote={bool(remote)} remote_mode={remote_mode}"
    )
    try:
        if parallel and (rung or action or target):
            console.print(
                "[red]Do not combine --parallel with --rung/--action/--target[/red]"
            )
            raise typer.Exit(code=1)
        if parallel:
            from search.saturday.cycle import run_saturday_parallel

            records = run_saturday_parallel(
                repo_root=repo_root,
                config_file=config,
                dry_run=dry_run,
                remote=remote,
                remote_mode=remote_mode,
            )
            console.print_json(data=records)
        else:
            from search.saturday.cycle import run_saturday_cycle

            record = run_saturday_cycle(
                repo_root=repo_root,
                config_file=config,
                rung=rung,
                action=action,
                target=target,
                dry_run=dry_run,
                remote=remote,
                remote_mode=remote_mode,
            )
            console.print_json(data=record)
        console.print("[bold green]Cycle complete[/bold green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command("loop")
def loop_cmd(
    cycles: Optional[int] = typer.Option(
        None,
        "--cycles",
        "-n",
        help="Number of wakes (0 or omit for config default; 0 means until Ctrl-C)",
    ),
    sleep: Optional[int] = typer.Option(
        None,
        "--sleep",
        "-s",
        help="Optional seconds between wakes (default 0: immediate next wake)",
    ),
    parallel: bool = typer.Option(
        False,
        "--parallel",
        help="Each wake runs disjoint R2 and R5 cycles together",
    ),
    dry_run: bool = typer.Option(False, "--dry-run", help="Plan only; no LLM calls"),
    remote: bool = typer.Option(
        False,
        "--remote",
        help="Use OpenRouter for formalize/prove; needs OPENROUTER_API_KEY",
    ),
    remote_only: bool = typer.Option(
        False,
        "--remote-only",
        help="Alias for --remote (OpenRouter formalize only)",
    ),
    escalate: bool = typer.Option(
        False,
        "--escalate",
        help="With --remote: try local first, then OpenRouter on failure",
    ),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
):
    """
    Repeated saturday wakes with optional sleep between cycles.

    Default pacing: finish a wake, then start the next immediately.
    OpenRouter cooldown is per-request. Stop with Ctrl-C or a finite --cycles.

    Examples:
        satday loop --cycles 3
        satday loop --parallel --cycles 2 --remote
        satday loop --parallel --cycles 2 --remote --escalate
        satday loop --parallel --dry-run --cycles 1
    """
    console.print("[bold blue]SATurday local loop[/bold blue]")
    if remote_only:
        remote = True
    if remote and escalate:
        remote_mode = "escalate"
    elif remote or remote_only:
        remote_mode = "remote"
    else:
        remote_mode = None
    console.print(
        f"cycles={cycles} sleep={sleep} parallel={parallel} dry_run={dry_run} "
        f"remote={bool(remote)} remote_mode={remote_mode}"
    )
    try:
        from search.saturday.loop import run_saturday_loop

        waves = run_saturday_loop(
            repo_root=repo_root,
            config_file=config,
            cycles=cycles,
            sleep_seconds=sleep,
            parallel=parallel,
            dry_run=dry_run,
            remote=remote,
            remote_mode=remote_mode,
        )
        console.print_json(data=waves)
        console.print(f"[bold green]Loop complete wakes={len(waves)}[/bold green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command("dashboard")
def dashboard_cmd(
    host: str = typer.Option("127.0.0.1", "--host", help="Bind address"),
    port: int = typer.Option(8765, "--port", "-p", help="HTTP port"),
):
    """
    Local progress dashboard with kill switch and accepted-declaration tree.

    Open http://127.0.0.1:8765/ while satday auto runs. Preferred monitor for
    the saturday skill. Use the Accepted tree tab for allowlisted Lean decls
    grouped by ladder rung (from scripts/accepted_declarations.txt).

    Examples:
        satday dashboard
        satday dashboard --port 8765
    """
    console.print("[bold blue]SATurday dashboard[/bold blue]")
    console.print(f"Open http://{host}:{port}/  (Ctrl-C to stop dashboard)")
    try:
        from search.saturday.dashboard_server import run_dashboard

        run_dashboard(repo_root=repo_root, host=host, port=port)
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


@app.command("kill")
def kill_cmd(
    reason: str = typer.Option(
        "operator kill",
        "--reason",
        "-r",
        help="Why auto should stop",
    ),
):
    """Engage the satday auto kill switch (checked each wake)."""
    from search.saturday.control import engage_kill

    state = engage_kill(repo_root, reason, source="cli")
    console.print(f"[bold red]Kill engaged[/bold red]: {state.reason}")
    console.print("Auto will stop at the next wake boundary.")


@app.command("unkill")
def unkill_cmd():
    """Clear the satday auto kill switch so auto can run again."""
    from search.saturday.control import clear_kill

    clear_kill(repo_root)
    console.print("[bold green]Kill cleared[/bold green]. You can run satday auto again.")


proof_source_app = typer.Typer(
    name="proof-source",
    help="Vendor and inspect foreign ITP proof sources for loop native import",
    no_args_is_help=True,
)
app.add_typer(proof_source_app, name="proof-source")


@proof_source_app.command("status")
def proof_source_status_cmd(
    source_id: Optional[str] = typer.Argument(
        None,
        help="Catalog id (default: show all entries)",
    ),
    json_out: bool = typer.Option(
        False,
        "--json",
        help="Emit machine readable JSON",
    ),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
):
    """
    Show readiness of cached proof sources (LICENSE, SOURCE.json, .thy files).

    Examples:
        satday proof-source status
        satday proof-source status afp-expander-graphs-mgg
        satday proof-source status --json
    """
    from search.saturday import proof_source as ps

    console.print("[bold blue]SATurday proof-source status[/bold blue]")
    try:
        cfg = ps.load_proof_import_config(repo_root)
        if not cfg.enabled:
            console.print("[yellow]proof_import.enabled=false in config[/yellow]")
        if source_id:
            entry = ps.entry_by_id(cfg, source_id)
            rows = [ps.status_for_entry(repo_root, cfg, entry)]
        else:
            rows = ps.status_all(repo_root, cfg)
        if json_out:
            console.print_json(data=[r.to_dict() for r in rows])
            return
        table = Table(title="Proof sources")
        table.add_column("id")
        table.add_column("ready")
        table.add_column("thy")
        table.add_column("license")
        table.add_column("blockers")
        for r in rows:
            table.add_row(
                r.id,
                "yes" if r.ready else "no",
                str(r.thy_count),
                "ok" if r.license_ok else "missing",
                "; ".join(r.blockers) if r.blockers else "-",
            )
        console.print(table)
        for r in rows:
            if not r.ready and r.id:
                entry = ps.entry_by_id(cfg, r.id)
                console.print(ps.vendor_instructions(entry))
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
        raise typer.Exit(code=1)


@proof_source_app.command("fetch")
def proof_source_fetch_cmd(
    source_id: str = typer.Argument(..., help="Catalog id to vendor"),
    from_dir: Optional[Path] = typer.Option(
        None,
        "--from-dir",
        help="Offline: copy Isabelle session dir (recommended)",
    ),
    network: bool = typer.Option(
        False,
        "--network",
        help="Download catalog fetch_url (requires allow_network_fetch or --force)",
    ),
    force: bool = typer.Option(
        False,
        "--force",
        help="With --network: allow fetch even if allow_network_fetch is false",
    ),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
):
    """
    Populate search/proof_sources/<root>/ from a local AFP path or network archive.

    Offline (preferred):
        satday proof-source fetch afp-expander-graphs-mgg \\
          --from-dir /path/to/afp/thys/Expander_Graphs

    Network (opt in):
        satday proof-source fetch afp-expander-graphs-mgg --network
    """
    from search.saturday import proof_source as ps

    console.print(f"[bold blue]SATurday proof-source fetch[/bold blue] id={source_id}")
    try:
        cfg = ps.load_proof_import_config(repo_root)
        if from_dir is not None:
            st = ps.fetch_from_dir(repo_root, source_id, from_dir, cfg)
        elif network:
            st = ps.fetch_network(repo_root, source_id, cfg, force=force)
        else:
            entry = ps.entry_by_id(cfg, source_id)
            console.print(
                "[yellow]Provide --from-dir PATH or --network. Offline vendor steps:[/yellow]"
            )
            console.print(ps.vendor_instructions(entry))
            raise typer.Exit(code=2)
        console.print(
            f"ready={st.ready} thy_count={st.thy_count} root={st.root}"
        )
        if st.blockers:
            console.print(f"[yellow]blockers:[/yellow] {'; '.join(st.blockers)}")
            raise typer.Exit(code=1)
        console.print("[bold green]Proof source ready[/bold green]")
    except typer.Exit:
        raise
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
        raise typer.Exit(code=1)


@proof_source_app.command("ladder")
def proof_source_ladder_cmd(
    source_id: str = typer.Argument(..., help="Catalog id to ladderize"),
    theories: Optional[str] = typer.Option(
        None,
        "--theories",
        help="Comma-separated theory stems (default: catalog primary_theories)",
    ),
    kinds: Optional[str] = typer.Option(
        None,
        "--kinds",
        help="Comma-separated decl kinds (default: lemma,theorem,definition,fun,...)",
    ),
    max_steps: Optional[int] = typer.Option(
        None,
        "--max-steps",
        help="Cap number of micro steps (Frontier pins still appended)",
    ),
    name_pattern: Optional[str] = typer.Option(
        None,
        "--name-pattern",
        help="Regex filter on foreign decl names",
    ),
    merge: bool = typer.Option(
        True,
        "--merge/--no-merge",
        help="Merge with existing accepted.json (keep done steps)",
    ),
    dry_run: bool = typer.Option(
        False,
        "--dry-run",
        help="Print summary without writing accepted.json",
    ),
    json_out: bool = typer.Option(
        False,
        "--json",
        help="Emit plan JSON to stdout",
    ),
    config: Optional[Path] = typer.Option(None, "--config", "-c", help="Config file path"),
):
    """
    Build a discrete import ladder from vendored foreign theories.

    Catalog-driven and reusable for any proof source: parse primary_theories
    into ordered unit=micro helper_insert steps, keep prior done steps, append
    maps_to_frontier as terminal sorry_replace pins.

    Examples:
        satday proof-source ladder afp-expander-graphs-mgg
        satday proof-source ladder afp-expander-graphs-mgg \\
          --theories Expander_Graphs_MGG,Expander_Graphs_Cheeger_Inequality \\
          --max-steps 40
    """
    from search.saturday import proof_source as ps
    from search.saturday.import_ladder import build_import_ladder

    console.print(
        f"[bold blue]SATurday proof-source ladder[/bold blue] id={source_id}"
    )
    try:
        cfg = ps.load_proof_import_config(repo_root)
        entry = ps.entry_by_id(cfg, source_id)
        st = ps.status_for_entry(repo_root, cfg, entry)
        if not st.ready:
            console.print(
                f"[yellow]Source not ready:[/yellow] {'; '.join(st.blockers)}"
            )
            raise typer.Exit(code=1)
        theory_list = (
            [t.strip() for t in theories.split(",") if t.strip()]
            if theories
            else None
        )
        kind_list = (
            [k.strip() for k in kinds.split(",") if k.strip()] if kinds else None
        )
        result = build_import_ladder(
            repo_root,
            cfg,
            entry,
            theories=theory_list,
            kinds=kind_list,
            max_steps=max_steps,
            name_pattern=name_pattern,
            merge_existing=merge,
            write=not dry_run,
        )
        console.print(
            f"decls={result.decls_extracted} steps={result.steps_emitted} "
            f"done_kept={result.steps_kept_done} theories={result.theories}"
        )
        if result.path:
            console.print(f"wrote {result.path}")
        elif dry_run:
            console.print("[yellow]dry-run: plan not written[/yellow]")
        nxt = None
        for step in result.plan.get("steps") or []:
            if str(step.get("status", "pending")) != "done":
                nxt = step
                break
        if nxt:
            console.print(
                f"next step id={nxt.get('id')} lean={nxt.get('lean_name')} "
                f"fill={nxt.get('fill_mode')}"
            )
        if json_out:
            console.print_json(data=result.plan)
    except typer.Exit:
        raise
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
        raise typer.Exit(code=1)


@app.command("status")
def status_cmd(
    json_out: bool = typer.Option(
        False,
        "--json",
        help="Emit machine readable JSON instead of tables",
    ),
):
    """
    Review saturday ladder status: completed rungs and progress toward P vs NP.

    Reads rung memories under docs/ladder/rungs/ and recent lines from
    search/logs/saturday_sessions.jsonl. Does not call an LLM.

    Examples:
        satday status
        satday status --json
        satday dashboard
    """
    console.print("[bold blue]SATurday ladder status[/bold blue]")
    try:
        from search.saturday.status import build_saturday_status, status_to_dict
        from search.saturday.progress import build_progress_snapshot

        status = build_saturday_status(repo_root)
        payload = status_to_dict(status)
        if json_out:
            console.print_json(data=build_progress_snapshot(repo_root))
            return

        table = Table(title="Ladder rungs")
        table.add_column("Rung", style="cyan")
        table.add_column("Title")
        table.add_column("Status", style="magenta")
        table.add_column("Memory")
        for row in status.rungs:
            table.add_row(row.rung_id, row.title, row.status, row.memory)
        console.print(table)

        console.print("\n[bold]Counts[/bold]")
        for key in sorted(status.counts):
            console.print(f"  {key}: {status.counts[key]}")

        console.print("\n[bold]Certified[/bold]")
        if status.certified:
            for rid in status.certified:
                console.print(f"  {rid}")
        else:
            console.print("  (none)")

        console.print("\n[bold]Active work[/bold]")
        if status.active_work:
            for rid in status.active_work:
                console.print(f"  {rid}")
        else:
            console.print("  (none)")

        nxt = status.next_cycle
        console.print("\n[bold]Suggested next cycle[/bold]")
        console.print(f"  rung: {nxt['rung']}")
        console.print(f"  action: {nxt['action_type']}")
        console.print(f"  target: {nxt['target']}")
        console.print(f"  rationale: {nxt['rationale']}")

        console.print("\n[bold]Parallel paths[/bold]")
        if status.parallel_paths:
            for path in status.parallel_paths:
                console.print(
                    f"  [{path.get('workstream') or '-'}] "
                    f"{path['rung']} -> {path['action_type']}"
                )
        else:
            console.print("  (none; only serial next cycle)")

        console.print("\n[bold]Suggested next commands[/bold]")
        for cmd in status.suggested_commands:
            console.print(f"  {cmd}")

        console.print("\n[bold]Toward P vs NP (summit)[/bold]")
        console.print(f"  {status.toward_p_vs_np}")
        console.print(f"  R4 certified: {status.summit.r4_certified}")
        console.print(f"  R5 certified: {status.summit.r5_certified}")
        console.print(f"  Summit ready: {status.summit.summit_ready}")
        if status.summit.blockers:
            console.print("  Blockers:")
            for blocker in status.summit.blockers:
                console.print(f"    - {blocker}")

        if status.last_session:
            console.print("\n[bold]Last saturday session[/bold]")
            console.print(
                f"  rung={status.last_session.get('rung')} "
                f"action={status.last_session.get('action_type')} "
                f"result={status.last_session.get('result')} "
                f"gate={status.last_session.get('gate_pending')}"
            )

        console.print("\n[bold green]Status complete[/bold green]")
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}", style="red")
        raise typer.Exit(code=1)


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

