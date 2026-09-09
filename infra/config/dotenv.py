"""
Minimal .env loader (no third party dependency).

Loads KEY=VALUE pairs from repo_root/.env into os.environ without
overwriting variables already set in the process environment.
Never prints secret values.
"""

from __future__ import annotations

import os
from pathlib import Path


def load_dotenv(repo_root: Path | None = None, filename: str = ".env") -> Path | None:
    """
    Load dotenv file if present.

    Returns the path loaded, or None if missing.
    """
    if repo_root is None:
        here = Path(__file__).resolve()
        for parent in [here] + list(here.parents):
            if (parent / ".git").exists():
                repo_root = parent
                break
        if repo_root is None:
            repo_root = Path.cwd()
    path = Path(repo_root) / filename
    if not path.is_file():
        print(f"[dotenv] no {filename} at {path}")
        return None
    loaded = 0
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if "=" not in line:
            continue
        key, _, value = line.partition("=")
        key = key.strip()
        value = value.strip().strip("'").strip('"')
        if not key:
            continue
        if key in os.environ and os.environ.get(key, "") != "":
            continue
        os.environ[key] = value
        loaded += 1
    print(f"[dotenv] loaded {loaded} keys from {path.name} (existing env wins)")
    return path
