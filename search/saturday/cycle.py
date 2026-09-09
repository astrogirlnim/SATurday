"""
One local saturday cycle: load context, choose, act, append memory, session record.

Canonical offline entrypoint for option A (CLI + localhost models).
Supports optional parallel disjoint workstreams (R2 + R5).
"""

from __future__ import annotations

import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, List, Optional

from infra.config.loader import load_config
from infra.config.schemas import SaturdayConfig, SaturdayLoopConfig
from search.llm.client import LocalLLMClient
from search.saturday.actions import run_action
from search.saturday.chooser import (
    ActionChoice,
    choose_rung_and_action,
    list_parallel_choices,
)
from search.saturday.context import (
    append_rung_memory,
    append_session_record,
    load_cycle_context,
)
from search.saturday.ui import announce


def run_saturday_cycle(
    repo_root: Optional[Path] = None,
    config_file: Optional[Path] = None,
    rung: Optional[str] = None,
    action: Optional[str] = None,
    target: Optional[str] = None,
    dry_run: bool = False,
    workstream_note: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Execute exactly one saturday session and stop.

    Returns the session record dict.
    """
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    repo_root = Path(repo_root)
    print(f"[saturday.cycle] start repo_root={repo_root} dry_run={dry_run}")

    config: SaturdayConfig = load_config(config_file=config_file, repo_root=repo_root)
    loop_cfg: SaturdayLoopConfig = config.saturday_loop
    if not loop_cfg.enabled:
        raise RuntimeError("saturday_loop.enabled is false in config")

    print(
        f"[saturday.cycle] loop endpoint={loop_cfg.endpoint} "
        f"api_style={loop_cfg.api_style} require_local={loop_cfg.require_local}"
    )

    ctx = load_cycle_context(repo_root)
    choice = choose_rung_and_action(
        ctx,
        rung_override=rung,
        action_override=action,
        target_override=target,
    )
    return _execute_choice(
        repo_root=repo_root,
        loop_cfg=loop_cfg,
        choice=choice,
        dry_run=dry_run,
        workstream_note=workstream_note or choice.workstream,
    )


def _execute_choice(
    repo_root: Path,
    loop_cfg: SaturdayLoopConfig,
    choice: ActionChoice,
    dry_run: bool,
    workstream_note: Optional[str],
) -> Dict[str, Any]:
    """Run one already chosen action (serial or one parallel worker)."""
    print(
        f"[saturday.cycle] choice rung={choice.rung} action={choice.action_type} "
        f"target={choice.target!r} workstream={workstream_note}"
    )
    announce(
        f"[{workstream_note or choice.workstream}] Starting {choice.action_type} "
        f"on {choice.rung}: {choice.target}"
    )
    announce(f"[{workstream_note or choice.workstream}] Why: {choice.rationale}")
    # Fresh context per worker so parallel paths do not share RungState buffers
    ctx = load_cycle_context(repo_root)
    if choice.rung not in ctx.rungs:
        raise RuntimeError(f"Rung missing from context: {choice.rung}")

    if dry_run:
        record = {
            "session_id": str(int(time.time())),
            "rung": choice.rung,
            "action_type": choice.action_type,
            "target": choice.target,
            "result": "partial",
            "artifact_refs": [],
            "gate_pending": "none",
            "next_recommended_action": choice.action_type,
            "timestamp": str(int(time.time())),
            "notes": _notes(f"dry_run: {choice.rationale}", workstream_note),
            "dry_run": True,
            "workstream": workstream_note,
        }
        print(f"[saturday.cycle] dry_run record={record}")
        return record

    client = None
    if choice.action_type != "falsify":
        client = LocalLLMClient(
            endpoint=loop_cfg.endpoint,
            api_style=loop_cfg.api_style,
            timeout_seconds=loop_cfg.timeout_seconds,
            require_local=loop_cfg.require_local,
        )

    result = run_action(ctx, choice, loop_cfg, client)
    print(
        f"[saturday.cycle] action done status={result.status} "
        f"gate={result.gate_pending} next={result.next_recommended_action}"
    )
    announce(
        f"[{workstream_note or choice.workstream}] Finished {choice.action_type}: "
        f"status={result.status}, next={result.next_recommended_action}, "
        f"gate={result.gate_pending}"
    )

    append_rung_memory(ctx.rungs[choice.rung], result.memory_entry)

    session_id = str(int(time.time() * 1000))
    record: Dict[str, Any] = {
        "session_id": session_id,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "rung": choice.rung,
        "action_type": choice.action_type,
        "target": choice.target,
        "result": result.status,
        "artifact_refs": result.artifact_refs,
        "gate_pending": result.gate_pending,
        "next_recommended_action": result.next_recommended_action,
        "timestamp": session_id,
        "notes": _notes(result.notes, workstream_note),
        "runner": "local_cli",
        "workstream": workstream_note,
        "models": {
            "prove": loop_cfg.prove.model,
            "formalize": loop_cfg.formalize.model,
            "audit": loop_cfg.audit.model,
        },
    }
    append_session_record(repo_root, record, loop_cfg.sessions_path)
    print(f"[saturday.cycle] session record written id={session_id}")
    return record


def run_saturday_parallel(
    repo_root: Optional[Path] = None,
    config_file: Optional[Path] = None,
    dry_run: bool = False,
) -> List[Dict[str, Any]]:
    """
    Run one cycle on each disjoint parallel workstream (typically R2 and R5).

    Each path still obeys the one rung / one action / one session record contract.
    """
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    repo_root = Path(repo_root)
    print(f"[saturday.cycle] parallel start repo_root={repo_root} dry_run={dry_run}")
    announce("Loading ladder context and picking disjoint workstreams (usually R2 + R5).")

    config: SaturdayConfig = load_config(config_file=config_file, repo_root=repo_root)
    loop_cfg: SaturdayLoopConfig = config.saturday_loop
    if not loop_cfg.enabled:
        raise RuntimeError("saturday_loop.enabled is false in config")

    ctx = load_cycle_context(repo_root)
    choices = list_parallel_choices(ctx)
    if not choices:
        announce("No parallel workstreams ready; falling back to a single cycle.")
        print("[saturday.cycle] no parallel workstreams actionable; falling back to serial")
        return [run_saturday_cycle(repo_root=repo_root, config_file=config_file, dry_run=dry_run)]

    if len(choices) == 1:
        announce(f"Only one workstream ready: {choices[0].workstream} on {choices[0].rung}.")
        print("[saturday.cycle] only one parallel path; running serial")
        c0 = choices[0]
        return [
            run_saturday_cycle(
                repo_root=repo_root,
                config_file=config_file,
                rung=c0.rung,
                action=c0.action_type,
                target=c0.target,
                dry_run=dry_run,
                workstream_note=c0.workstream,
            )
        ]

    records: List[Dict[str, Any]] = []
    announce(
        "Running in parallel: "
        + ", ".join(f"{c.workstream}={c.action_type}/{c.rung}" for c in choices)
    )
    print(f"[saturday.cycle] launching {len(choices)} parallel workers")
    with ThreadPoolExecutor(max_workers=len(choices)) as pool:
        futures = {
            pool.submit(
                _execute_choice,
                repo_root,
                loop_cfg,
                choice,
                dry_run,
                choice.workstream,
            ): choice
            for choice in choices
        }
        for fut in as_completed(futures):
            choice = futures[fut]
            try:
                record = fut.result()
                records.append(record)
                print(
                    f"[saturday.cycle] parallel done workstream={choice.workstream} "
                    f"rung={choice.rung} result={record.get('result')}"
                )
            except Exception as exc:
                print(
                    f"[saturday.cycle] parallel FAILED workstream={choice.workstream}: {exc}"
                )
                records.append(
                    {
                        "session_id": str(int(time.time() * 1000)),
                        "rung": choice.rung,
                        "action_type": choice.action_type,
                        "target": choice.target,
                        "result": "blocked",
                        "artifact_refs": [],
                        "gate_pending": "none",
                        "next_recommended_action": choice.action_type,
                        "timestamp": str(int(time.time() * 1000)),
                        "notes": _notes(f"parallel worker error: {exc}", choice.workstream),
                        "workstream": choice.workstream,
                        "runner": "local_cli",
                        "error": str(exc),
                    }
                )
    print(f"[saturday.cycle] parallel complete records={len(records)}")
    return records


def _notes(body: str, workstream: Optional[str]) -> str:
    if workstream:
        return f"workstream: {workstream}. {body}"
    return body


def main() -> None:
    """CLI: python -m search.saturday.cycle [--dry-run] [--parallel] ..."""
    import argparse

    parser = argparse.ArgumentParser(description="Run one local saturday cycle")
    parser.add_argument("--config", type=Path, default=None)
    parser.add_argument("--rung", type=str, default=None)
    parser.add_argument(
        "--action",
        type=str,
        choices=["prove", "formalize", "falsify", "audit"],
        default=None,
    )
    parser.add_argument("--target", type=str, default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--parallel",
        action="store_true",
        help="Run all disjoint workstream cycles (R2 and R5) together",
    )
    args = parser.parse_args()
    if args.parallel:
        records = run_saturday_parallel(
            config_file=args.config,
            dry_run=args.dry_run,
        )
        print("[saturday.cycle] done parallel")
        print(records)
    else:
        record = run_saturday_cycle(
            config_file=args.config,
            rung=args.rung,
            action=args.action,
            target=args.target,
            dry_run=args.dry_run,
        )
        print("[saturday.cycle] done")
        print(record)


if __name__ == "__main__":
    main()
