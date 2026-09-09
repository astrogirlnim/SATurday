"""
LLM HTTP client (stdlib only).

Supports:
- Ollama native POST {endpoint}/api/generate
- OpenAI compatible POST {endpoint}/v1/chat/completions
  (also {endpoint}/chat/completions when endpoint already ends in /v1)
- Optional Bearer auth for OpenRouter / hosted OpenAI compatible APIs

Default require_local=True refuses non loopback hosts (offline policy).
Remote OpenRouter use is opt in via saturday_loop.remote + satday --remote.
"""

from __future__ import annotations

import json
import threading
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any, Dict, List, Optional
from urllib.parse import urlparse


_LOCAL_HOSTS = frozenset({"localhost", "127.0.0.1", "::1", "0.0.0.0"})

# One inference at a time across local and remote callers in this process
_INFERENCE_LOCK = threading.Lock()
_INFERENCE_LOCK_HOLDER = threading.local()


@dataclass
class LLMRequest:
    """One generation request."""

    model: str
    prompt: str
    system: Optional[str] = None
    temperature: float = 0.1
    num_predict: int = 8192
    api_style: str = "ollama"  # ollama | openai_compatible


@dataclass
class LLMResponse:
    """Normalized generation response."""

    text: str
    model: str
    elapsed_seconds: float
    raw: Dict[str, Any]


class LocalLLMClient:
    """
    HTTP client for local or explicitly enabled remote inference.

    Variables:
    - endpoint: base URL
    - api_style: ollama | openai_compatible
    - timeout_seconds
    - require_local: reject remote hosts when True
    - api_key: optional Bearer token (never logged)
    - extra_headers: optional provider headers (OpenRouter referer/title)
    """

    def __init__(
        self,
        endpoint: str = "http://localhost:11434",
        api_style: str = "ollama",
        timeout_seconds: int = 600,
        require_local: bool = True,
        api_key: Optional[str] = None,
        extra_headers: Optional[Dict[str, str]] = None,
        label: str = "local",
    ) -> None:
        self.endpoint = endpoint.rstrip("/")
        self.api_style = api_style
        self.timeout_seconds = timeout_seconds
        self.require_local = require_local
        self.api_key = api_key
        self.extra_headers = dict(extra_headers or {})
        self.label = label
        print(
            f"[LocalLLMClient] init label={self.label} endpoint={self.endpoint} "
            f"api_style={self.api_style} timeout={self.timeout_seconds}s "
            f"require_local={self.require_local} "
            f"auth={'yes' if self.api_key else 'no'}"
        )
        if self.require_local:
            self._assert_local(self.endpoint)

    def _assert_local(self, endpoint: str) -> None:
        """Fail fast if endpoint is not a loopback host."""
        parsed = urlparse(endpoint)
        host = (parsed.hostname or "").lower()
        print(f"[LocalLLMClient] host check hostname={host!r}")
        if host not in _LOCAL_HOSTS:
            raise ValueError(
                f"Non local LLM endpoint blocked by offline policy: {endpoint}. "
                "Use saturday_loop.remote with satday --remote for OpenRouter."
            )

    def generate(self, request: LLMRequest) -> LLMResponse:
        """Run one completion and return normalized text."""
        style = request.api_style or self.api_style
        print(
            f"[LocalLLMClient] generate label={self.label} model={request.model} "
            f"style={style} prompt_chars={len(request.prompt)} "
            f"temp={request.temperature} num_predict={request.num_predict}"
        )
        held = getattr(_INFERENCE_LOCK_HOLDER, "held", False)
        if held:
            return self._generate_unlocked(request, style)
        print("[LocalLLMClient] waiting for inference lock")
        with _INFERENCE_LOCK:
            _INFERENCE_LOCK_HOLDER.held = True
            try:
                print("[LocalLLMClient] acquired inference lock")
                return self._generate_unlocked(request, style)
            finally:
                _INFERENCE_LOCK_HOLDER.held = False
                print("[LocalLLMClient] released inference lock")

    def _generate_unlocked(self, request: LLMRequest, style: str) -> LLMResponse:
        if style == "openai_compatible":
            return self._chat_completions(request)
        if style == "ollama":
            return self._ollama_generate(request)
        raise ValueError(f"Unknown api_style: {style}")

    def _chat_url(self) -> str:
        """OpenAI compatible chat completions URL."""
        base = self.endpoint.rstrip("/")
        if base.endswith("/v1"):
            return f"{base}/chat/completions"
        return f"{base}/v1/chat/completions"

    def _ollama_generate(self, request: LLMRequest) -> LLMResponse:
        """POST /api/generate (Ollama native)."""
        url = f"{self.endpoint}/api/generate"
        prompt = request.prompt
        if request.system:
            prompt = f"{request.system}\n\n{request.prompt}"
        payload: Dict[str, Any] = {
            "model": request.model,
            "prompt": prompt,
            "stream": False,
            "options": {
                "temperature": request.temperature,
                "num_predict": request.num_predict,
            },
        }
        raw = self._post_json(url, payload)
        text = raw.get("response", "")
        if not isinstance(text, str):
            text = str(text)
        thinking = raw.get("thinking")
        if thinking and not text:
            text = str(thinking)
        elapsed = float(raw.get("_elapsed_seconds", 0.0))
        print(f"[LocalLLMClient] ollama done chars={len(text)} elapsed={elapsed:.1f}s")
        return LLMResponse(text=text, model=request.model, elapsed_seconds=elapsed, raw=raw)

    def _chat_completions(self, request: LLMRequest) -> LLMResponse:
        """POST chat/completions (Ollama OpenAI compat, OpenRouter, etc.)."""
        url = self._chat_url()
        messages: List[Dict[str, str]] = []
        if request.system:
            messages.append({"role": "system", "content": request.system})
        messages.append({"role": "user", "content": request.prompt})
        payload: Dict[str, Any] = {
            "model": request.model,
            "messages": messages,
            "temperature": request.temperature,
            "max_tokens": request.num_predict,
            "stream": False,
        }
        raw = self._post_json(url, payload)
        choices = raw.get("choices") or []
        text = ""
        if choices:
            message = choices[0].get("message") or {}
            text = message.get("content") or ""
            # Some models put reasoning separately
            if not text and message.get("reasoning"):
                text = str(message.get("reasoning"))
        if not isinstance(text, str):
            text = str(text)
        elapsed = float(raw.get("_elapsed_seconds", 0.0))
        print(f"[LocalLLMClient] chat done chars={len(text)} elapsed={elapsed:.1f}s")
        return LLMResponse(text=text, model=request.model, elapsed_seconds=elapsed, raw=raw)

    def _post_json(self, url: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """POST JSON and parse object response."""
        body = json.dumps(payload).encode("utf-8")
        headers = {"Content-Type": "application/json"}
        headers.update(self.extra_headers)
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        print(f"[LocalLLMClient] POST {url} bytes={len(body)} auth={'yes' if self.api_key else 'no'}")
        req = urllib.request.Request(
            url,
            data=body,
            headers=headers,
            method="POST",
        )
        started = time.time()
        try:
            with urllib.request.urlopen(req, timeout=self.timeout_seconds) as resp:
                raw_bytes = resp.read()
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            print(f"[LocalLLMClient] HTTP {exc.code}: {detail[:500]}")
            raise RuntimeError(f"LLM HTTP {exc.code} at {url}: {detail[:500]}") from exc
        except urllib.error.URLError as exc:
            print(f"[LocalLLMClient] URL error: {exc}")
            raise RuntimeError(
                f"LLM unreachable at {url}. Check local server or OpenRouter network."
            ) from exc
        elapsed = time.time() - started
        print(f"[LocalLLMClient] response bytes={len(raw_bytes)} elapsed={elapsed:.1f}s")
        data = json.loads(raw_bytes.decode("utf-8"))
        if not isinstance(data, dict):
            raise RuntimeError(f"LLM returned non object JSON from {url}")
        data["_elapsed_seconds"] = elapsed
        return data
