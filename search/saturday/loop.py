"""
Local saturday wake loop: repeated cycles with event-driven pacing.

One cycle (or one parallel wave) per wake, then immediately start the next
unless an optional --sleep override or config loop_sleep_seconds is set.
OpenRouter rate pacing lives in the remote LLM client, not here.
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


def run_saturday_loop(
    repo_root: Optional[Path] = None,
    config_file: Optional[Path] = None,
    cycles: Optional[int] = None,
    sleep_seconds: Optional[int] = None,
    parallel: Optional[bool] = None,
    dry_run: bool = False,
    remote: bool = False,
    remote_mode: Optional[str] = None,
) -> List[List[Dict[str, Any]]]:
    """
    Run repeated saturday wakes.

    cycles: None uses config.loop_max_cycles; 0 means until interrupted.
    parallel: None uses config.loop_parallel_default.
    sleep_seconds: optional override; 0 means no inter-wake sleep (default).
    remote: enable OpenRouter for formalize (needs OPENROUTER_API_KEY).
    """
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[2]
    repo_root = Path(repo_root)
    config = load_config(config_file=config_file, repo_root=repo_root)
    loop_cfg: SaturdayLoopConfig = config.saturday_loop

    max_cycles = loop_cfg.loop_max_cycles if cycles is None else cycles
    # Default 0: callback-style pacing (finish wave -> next wake)
    base_sleep = loop_cfg.loop_sleep_seconds if sleep_seconds is None else sleep_seconds
    use_parallel = loop_cfg.loop_parallel_default if parallel is None else parallel

    banner("SATurday auto loop")
    announce(
        "This loop explores proofs, applies Lean drafts, reverts on compile "
        "failure, and feeds errors into the next wake. Stop with Ctrl-C."
    )
    announce(
        f"Settings: max_cycles={max_cycles or 'until interrupted'} "
        f"inter_wake_sleep={base_sleep}s parallel={use_parallel} dry_run={dry_run} "
        f"remote={remote}"
    )
    if base_sleep <= 0:
        announce(
            "Pacing: next wake starts immediately when the prior wave finishes "
            "(OpenRouter cooldown is per-request in the remote client)."
        )
    if remote:
        from search.saturday.llm_factory import enable_remote_on_config

        enable_remote_on_config(loop_cfg, mode=remote_mode or "remote")
    print(
        f"[saturday.loop] start max_cycles={max_cycles} inter_wake_sleep={base_sleep} "
        f"parallel={use_parallel} dry_run={dry_run} remote={remote}"
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
                    remote=remote,
                    remote_mode=remote_mode,
                )
            else:
                records = [
                    run_saturday_cycle(
                        repo_root=repo_root,
                        config_file=config_file,
                        dry_run=dry_run,
                        remote=remote,
                        remote_mode=remote_mode,
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

            if base_sleep > 0:
                announce(
                    f"Optional inter-wake sleep {base_sleep}s "
                    "(CLI --sleep or loop_sleep_seconds override)."
                )
                print(f"[saturday.loop] sleeping {base_sleep}s before next wake")
                time.sleep(base_sleep)
            else:
                announce("Starting next wake now (no inter-wake sleep).")
                print("[saturday.loop] immediate next wake (no sleep)")
    except KeyboardInterrupt:
        announce(f"Interrupted after wake {wake}. Progress so far is in rung memory and sessions.")
        print(f"[saturday.loop] interrupted after wake={wake}")

    announce(f"Loop finished. Completed wakes: {len(waves)}.")
    print(f"[saturday.loop] done waves={len(waves)}")
    return waves
