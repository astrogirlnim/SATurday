"""
Local saturday wake loop: repeated cycles with dynamic sleep between wakes.

Matches the saturday skill contract: one cycle (or one parallel wave) per wake,
then sleep, then wake again. Not a fixed while sleep 1800 loop with no stop.
Stop with Ctrl-C or --cycles N.
"""

from __future__ import annotations

import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from infra.config.loader import load_config
from infra.config.schemas import SaturdayLoopConfig
from search.saturday.cycle import run_saturday_cycle, run_saturday_parallel
from search.saturday.ui import announce, banner, summarize_wave


def suggest_sleep_seconds(records: List[Dict[str, Any]], default_sleep: int) -> int:
    """Pick next sleep from last wave results (light vs heavy)."""
    if not records:
        return default_sleep
    actions = {r.get("action_type") for r in records}
    results = {r.get("result") for r in records}
    if "falsify" in actions or "formalize" in actions:
        sleep = max(default_sleep, 120)
    elif "prove" in actions or "audit" in actions:
        sleep = max(30, min(default_sleep, 90))
    else:
        sleep = default_sleep
    if results <= {"blocked"}:
        sleep = max(sleep, 60)
    print(f"[saturday.loop] suggest_sleep={sleep}s actions={actions} results={results}")
    return sleep


def run_saturday_loop(
    repo_root: Optional[Path] = None,
    config_file: Optional[Path] = None,
    cycles: Optional[int] = None,
    sleep_seconds: Optional[int] = None,
    parallel: Optional[bool] = None,
    dry_run: bool = False,
) -> List[List[Dict[str, Any]]]:
    """
    Run repeated saturday wakes.

    cycles: None uses config.loop_max_cycles; 0 means until interrupted.
    parallel: None uses config.loop_parallel_default.
    """
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    repo_root = Path(repo_root)
    config = load_config(config_file=config_file, repo_root=repo_root)
    loop_cfg: SaturdayLoopConfig = config.saturday_loop

    max_cycles = loop_cfg.loop_max_cycles if cycles is None else cycles
    base_sleep = loop_cfg.loop_sleep_seconds if sleep_seconds is None else sleep_seconds
    use_parallel = loop_cfg.loop_parallel_default if parallel is None else parallel

    banner("SATurday auto loop")
    announce(
        "This loop explores proofs, applies Lean drafts, reverts on compile "
        "failure, and feeds errors into the next wake. Stop with Ctrl-C."
    )
    announce(
        f"Settings: max_cycles={max_cycles or 'until interrupted'} "
        f"base_sleep={base_sleep}s parallel={use_parallel} dry_run={dry_run}"
    )
    print(
        f"[saturday.loop] start max_cycles={max_cycles} base_sleep={base_sleep} "
        f"parallel={use_parallel} dry_run={dry_run}"
    )

    waves: List[List[Dict[str, Any]]] = []
    wake = 0
    try:
        while True:
            wake += 1
            banner(f"Wake {wake} starting")
            announce(
                "Choosing next workstreams, then running prove/formalize/"
                "falsify/audit as selected."
            )
            print(f"[saturday.loop] wake={wake}")
            if use_parallel:
                records = run_saturday_parallel(
                    repo_root=repo_root,
                    config_file=config_file,
                    dry_run=dry_run,
                )
            else:
                records = [
                    run_saturday_cycle(
                        repo_root=repo_root,
                        config_file=config_file,
                        dry_run=dry_run,
                    )
                ]
            waves.append(records)
            print(
                f"[saturday.loop] wake={wake} finished "
                f"results={[r.get('result') for r in records]}"
            )
            summarize_wave(wake, records)

            if max_cycles > 0 and wake >= max_cycles:
                announce(f"Reached configured max_cycles={max_cycles}. Stopping.")
                print(f"[saturday.loop] reached max_cycles={max_cycles}; stopping")
                break

            sleep_for = suggest_sleep_seconds(records, base_sleep)
            announce(
                f"Sleeping {sleep_for}s before the next wake "
                "(gives lake/model breathing room; errors stay on disk for retry)."
            )
            print(f"[saturday.loop] sleeping {sleep_for}s before next wake")
            time.sleep(sleep_for)
    except KeyboardInterrupt:
        announce(f"Interrupted after wake {wake}. Progress so far is in rung memory and sessions.")
        print(f"[saturday.loop] interrupted after wake={wake}")

    announce(f"Loop finished. Completed wakes: {len(waves)}.")
    print(f"[saturday.loop] done waves={len(waves)}")
    return waves
