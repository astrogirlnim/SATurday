"""
Build local and optional remote (OpenRouter) LLM clients for saturday.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Optional, Tuple

from infra.config.schemas import SaturdayLoopConfig, SaturdayRemoteConfig
from search.llm.client import LocalLLMClient
from search.saturday.ui import announce

# Env names (prefer these over YAML hardcoding)
_MODELS_DIR_ENV = "OLLAMA_MODELS"  # native Ollama store path
_MODELS_DIR_FALLBACK_ENV = "SATURDAY_MODELS_DIR"
_LOCAL_PROVE_MODEL_ENV = "SATURDAY_PROVE_MODEL"
_LOCAL_FORMALIZE_MODEL_ENV = "SATURDAY_FORMALIZE_MODEL"
_LOCAL_AUDIT_MODEL_ENV = "SATURDAY_AUDIT_MODEL"


def resolve_models_dir(
    repo_root: Path,
    models_dir: str = "",
) -> Tuple[Optional[Path], str]:
    """
    Resolve the local weight store path without moving files.

    Precedence:
      1. OLLAMA_MODELS (Ollama native)
      2. SATURDAY_MODELS_DIR
      3. saturday_loop.models_dir from config (relative to repo_root if not absolute)

    Returns (path_or_None, source_label). None means "leave Ollama's default alone"
    (~/.ollama/models). The loop never writes weights; it only names models over HTTP.
    """
    for env_name in (_MODELS_DIR_ENV, _MODELS_DIR_FALLBACK_ENV):
        raw = os.environ.get(env_name, "").strip()
        if raw:
            path = Path(raw).expanduser()
            if not path.is_absolute():
                path = (Path(repo_root) / path).resolve()
            else:
                path = path.resolve()
            print(f"[saturday.models] resolve source={env_name} path={path}")
            return path, env_name

    raw = (models_dir or "").strip()
    if not raw:
        print(
            "[saturday.models] resolve source=default "
            "path=None (Ollama home store; set OLLAMA_MODELS to use this volume)"
        )
        return None, "default"

    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = (Path(repo_root) / path).resolve()
    else:
        path = path.resolve()
    print(f"[saturday.models] resolve source=config.models_dir path={path}")
    return path, "config.models_dir"


def apply_local_model_overrides(loop_cfg: SaturdayLoopConfig) -> None:
    """Apply SATURDAY_*_MODEL and SATURDAY_NUM_CTX env overrides."""
    prove = os.environ.get(_LOCAL_PROVE_MODEL_ENV, "").strip()
    if prove:
        loop_cfg.prove.model = prove
        print(f"[saturday.llm] {_LOCAL_PROVE_MODEL_ENV}={prove}")
    formalize = os.environ.get(_LOCAL_FORMALIZE_MODEL_ENV, "").strip()
    if formalize:
        loop_cfg.formalize.model = formalize
        print(f"[saturday.llm] {_LOCAL_FORMALIZE_MODEL_ENV}={formalize}")
    audit = os.environ.get(_LOCAL_AUDIT_MODEL_ENV, "").strip()
    if audit:
        loop_cfg.audit.model = audit
        print(f"[saturday.llm] {_LOCAL_AUDIT_MODEL_ENV}={audit}")
    num_ctx_raw = os.environ.get("SATURDAY_NUM_CTX", "").strip()
    if num_ctx_raw:
        try:
            loop_cfg.num_ctx = int(num_ctx_raw)
            print(f"[saturday.llm] SATURDAY_NUM_CTX={loop_cfg.num_ctx}")
        except ValueError:
            print(f"[saturday.llm] ignoring bad SATURDAY_NUM_CTX={num_ctx_raw!r}")


def announce_local_model_store(repo_root: Path, loop_cfg: SaturdayLoopConfig) -> None:
    """
    Log where weights should live. Does not migrate or symlink.

    Ollama reads OLLAMA_MODELS when `ollama serve` starts. Setting it only in
    this Python process does not retarget an already running daemon.
    """
    store, source = resolve_models_dir(repo_root, getattr(loop_cfg, "models_dir", "") or "")
    if store is None:
        announce(
            "Local weights: Ollama default (~/.ollama/models). "
            "To use the SATurday volume, set OLLAMA_MODELS before `ollama serve`."
        )
        return

    if source != _MODELS_DIR_ENV:
        # Make child `ollama` CLI calls see the same store. Restart serve with
        # this env for the daemon to pick it up.
        os.environ[_MODELS_DIR_ENV] = str(store)
        print(
            f"[saturday.models] exported {_MODELS_DIR_ENV}={store} "
            "(restart `ollama serve` if the daemon was already running)"
        )

    exists = store.is_dir()
    n_files = (
        sum(1 for p in store.rglob("*") if p.is_file()) if exists else 0
    )
    print(
        f"[saturday.models] store path={store} source={source} "
        f"exists={exists} files={n_files}"
    )
    announce(
        f"Local weight store ({source}): {store}. "
        f"Role models: prove={loop_cfg.prove.model} "
        f"formalize={loop_cfg.formalize.model} audit={loop_cfg.audit.model}."
    )
    if not exists or n_files == 0:
        announce(
            "Weight store is empty. Copy existing Ollama blobs there, or run "
            f"`OLLAMA_MODELS={store} ollama pull <model>` after restarting serve."
        )


def make_local_client(loop_cfg: SaturdayLoopConfig) -> LocalLLMClient:
    """Default localhost Ollama (or local OpenAI compatible) client."""
    return LocalLLMClient(
        endpoint=loop_cfg.endpoint,
        api_style=loop_cfg.api_style,
        timeout_seconds=loop_cfg.timeout_seconds,
        require_local=loop_cfg.require_local,
        label="local",
        num_ctx=getattr(loop_cfg, "num_ctx", None),
    )


def remote_config(loop_cfg: SaturdayLoopConfig) -> SaturdayRemoteConfig:
    return getattr(loop_cfg, "remote", None) or SaturdayRemoteConfig()


def make_remote_client(loop_cfg: SaturdayLoopConfig) -> LocalLLMClient:
    """
    OpenRouter (or other OpenAI compatible hosted) client.

    Reads API key from the env var named in remote.api_key_env.
    """
    from infra.config.dotenv import load_dotenv

    # Ensure .env is visible even if client is built before full config load
    load_dotenv()

    remote = remote_config(loop_cfg)
    # Allow .env / shell override of models without editing YAML
    formalize_override = os.environ.get("OPENROUTER_FORMALIZE_MODEL", "").strip()
    if formalize_override:
        remote.formalize_model = formalize_override
        print(f"[saturday.llm] OPENROUTER_FORMALIZE_MODEL={formalize_override}")
    prove_override = os.environ.get("OPENROUTER_PROVE_MODEL", "").strip()
    if prove_override:
        remote.prove_model = prove_override
        print(f"[saturday.llm] OPENROUTER_PROVE_MODEL={prove_override}")
    env_name = remote.api_key_env
    api_key = os.environ.get(env_name, "").strip()
    if not api_key:
        raise RuntimeError(
            f"Remote LLM enabled but {env_name} is empty. "
            f"Put it in repo .env or export {env_name}=sk-or-... then rerun with --remote."
        )
    announce(
        f"Remote LLM client ready ({remote.endpoint}, "
        f"formalize_model={remote.formalize_model}, "
        f"prove_model={remote.prove_model}). "
        "This spends OpenRouter credits."
    )
    headers = {
        "HTTP-Referer": remote.http_referer,
        "X-OpenRouter-Title": remote.app_title,
    }
    return LocalLLMClient(
        endpoint=remote.endpoint,
        api_style=remote.api_style,
        timeout_seconds=remote.timeout_seconds,
        require_local=False,
        api_key=api_key,
        extra_headers=headers,
        label="openrouter",
        min_request_interval_seconds=remote.min_request_interval_seconds,
        rate_limit_backoff_seconds=remote.rate_limit_backoff_seconds,
        rate_limit_retries=remote.rate_limit_retries,
    )


def enable_remote_on_config(loop_cfg: SaturdayLoopConfig, mode: Optional[str] = None) -> None:
    """Mutate loop config for a CLI --remote session."""
    remote = remote_config(loop_cfg)
    remote.enabled = True
    if mode in {"escalate", "remote"}:
        remote.mode = mode
    else:
        # CLI --remote default: skip weak local formalize
        remote.mode = remote.mode or "remote"
    loop_cfg.remote = remote
    announce(
        f"OpenRouter formalize ON (mode={remote.mode}, "
        f"formalize_model={remote.formalize_model})."
    )


def want_remote_formalize(loop_cfg: SaturdayLoopConfig) -> bool:
    remote = remote_config(loop_cfg)
    return bool(remote.enabled and remote.use_for_formalize)


def want_remote_prove(loop_cfg: SaturdayLoopConfig) -> bool:
    remote = remote_config(loop_cfg)
    return bool(remote.enabled and remote.use_for_prove)


def want_remote_audit(loop_cfg: SaturdayLoopConfig) -> bool:
    remote = remote_config(loop_cfg)
    return bool(remote.enabled and remote.use_for_audit)


def remote_model_for(loop_cfg: SaturdayLoopConfig, role: str) -> str:
    """Pick OpenRouter model slug for prove|formalize|audit."""
    remote = remote_config(loop_cfg)
    if role == "formalize":
        return remote.formalize_model
    if role == "prove":
        return remote.prove_model
    if role == "audit":
        return remote.audit_model
    raise ValueError(f"unknown role: {role}")
