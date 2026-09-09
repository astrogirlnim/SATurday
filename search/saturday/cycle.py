"""
One local saturday cycle: load context, choose, act, append memory, session record.

Canonical offline entrypoint for option A (CLI + localhost models).
"""

from __future__ import annotations

import time
from pathlib import Path
from typing import Any, Dict, Optional

from infra.config.loader import load_config
from infra.config.schemas import SaturdayConfig, SaturdayLoopConfig
from search.llm.client import LocalLLMClient
from search.saturday.actions import run_action
from search.saturday.chooser import choose_rung_and_action
from search.saturday.context import (
    append_rung_memory,
    append_session_record,
    load_cycle_context,
)


def run_saturday_cycle(
    repo_root: Optional[Path] = None,
    config_file: Optional[Path] = None,
    rung: Optional[str] = None,
    action: Optional[str] = None,
    target: Optional[str] = None,
    dry_run: bool = False,
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
    print(
        f"[saturday.cycle] choice rung={choice.rung} action={choice.action_type} "
        f"target={choice.target!r}"
    )

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
            "notes": f"dry_run: {choice.rationale}",
            "dry_run": True,
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

    append_rung_memory(ctx.rungs[choice.rung], result.memory_entry)

    session_id = str(int(time.time()))
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
        "notes": result.notes,
        "runner": "local_cli",
        "models": {
            "prove": loop_cfg.prove.model,
            "formalize": loop_cfg.formalize.model,
            "audit": loop_cfg.audit.model,
        },
    }
    append_session_record(repo_root, record, loop_cfg.sessions_path)
    print(f"[saturday.cycle] session record written id={session_id}")
    return record


def main() -> None:
    """CLI: python -m search.saturday.cycle [--dry-run] [--rung ID] [--action TYPE]."""
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
    args = parser.parse_args()
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
