"""
Build local and optional remote (OpenRouter) LLM clients for saturday.
"""

from __future__ import annotations

import os
from typing import Optional

from infra.config.schemas import SaturdayLoopConfig, SaturdayRemoteConfig
from search.llm.client import LocalLLMClient
from search.saturday.ui import announce


def make_local_client(loop_cfg: SaturdayLoopConfig) -> LocalLLMClient:
    """Default localhost Ollama (or local OpenAI compatible) client."""
    return LocalLLMClient(
        endpoint=loop_cfg.endpoint,
        api_style=loop_cfg.api_style,
        timeout_seconds=loop_cfg.timeout_seconds,
        require_local=loop_cfg.require_local,
        label="local",
    )


def remote_config(loop_cfg: SaturdayLoopConfig) -> SaturdayRemoteConfig:
    return getattr(loop_cfg, "remote", None) or SaturdayRemoteConfig()


def make_remote_client(loop_cfg: SaturdayLoopConfig) -> LocalLLMClient:
    """
    OpenRouter (or other OpenAI compatible hosted) client.

    Reads API key from the env var named in remote.api_key_env.
    """
    remote = remote_config(loop_cfg)
    env_name = remote.api_key_env
    api_key = os.environ.get(env_name, "").strip()
    if not api_key:
        raise RuntimeError(
            f"Remote LLM enabled but {env_name} is empty. "
            f"Export {env_name}=sk-or-... then rerun with --remote."
        )
    announce(
        f"Remote LLM client ready ({remote.endpoint}). "
        "This spends OpenRouter credits; local remains default without --remote."
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
    )


def enable_remote_on_config(loop_cfg: SaturdayLoopConfig, mode: Optional[str] = None) -> None:
    """Mutate loop config for a CLI --remote session."""
    remote = remote_config(loop_cfg)
    remote.enabled = True
    if mode in {"escalate", "remote"}:
        remote.mode = mode
    loop_cfg.remote = remote
    announce(
        f"OpenRouter escalation ON (mode={remote.mode}, "
        f"formalize_model={remote.formalize_model})."
    )


def want_remote_formalize(loop_cfg: SaturdayLoopConfig) -> bool:
    remote = remote_config(loop_cfg)
    return bool(remote.enabled and remote.use_for_formalize)
