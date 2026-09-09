"""Local saturday research loop package (CLI + localhost LLMs)."""

from typing import Any

__all__ = ["run_saturday_cycle"]


def __getattr__(name: str) -> Any:
    if name == "run_saturday_cycle":
        from search.saturday.cycle import run_saturday_cycle

        return run_saturday_cycle
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
