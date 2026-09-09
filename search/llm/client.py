"""
Local LLM HTTP client (stdlib only).

Supports:
- Ollama native POST {endpoint}/api/generate
- OpenAI compatible POST {endpoint}/v1/chat/completions

Refuses non local hosts when require_local is True (default), matching the
repo offline and zero cost policy.
"""

from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any, Dict, List, Optional
from urllib.parse import urlparse


_LOCAL_HOSTS = frozenset({"localhost", "127.0.0.1", "::1", "0.0.0.0"})


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
    HTTP client for local inference servers.

    Variables consumed from config or callers:
    - endpoint: base URL, default http://localhost:11434
    - api_style: ollama | openai_compatible
    - timeout_seconds: urllib timeout
    - require_local: reject remote hosts when True
    """

    def __init__(
        self,
        endpoint: str = "http://localhost:11434",
        api_style: str = "ollama",
        timeout_seconds: int = 600,
        require_local: bool = True,
    ) -> None:
        self.endpoint = endpoint.rstrip("/")
        self.api_style = api_style
        self.timeout_seconds = timeout_seconds
        self.require_local = require_local
        print(
            f"[LocalLLMClient] init endpoint={self.endpoint} "
            f"api_style={self.api_style} timeout={self.timeout_seconds}s "
            f"require_local={self.require_local}"
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
                "Set saturday_loop.require_local=false only for an explicit LAN "
                "inference box you control."
            )

    def generate(self, request: LLMRequest) -> LLMResponse:
        """Run one completion and return normalized text."""
        style = request.api_style or self.api_style
        print(
            f"[LocalLLMClient] generate model={request.model} style={style} "
            f"prompt_chars={len(request.prompt)} temp={request.temperature} "
            f"num_predict={request.num_predict}"
        )
        if style == "openai_compatible":
            return self._chat_completions(request)
        if style == "ollama":
            return self._ollama_generate(request)
        raise ValueError(f"Unknown api_style: {style}")

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
        # DeepSeek R1 style fields when present
        thinking = raw.get("thinking")
        if thinking and not text:
            text = str(thinking)
        elapsed = float(raw.get("_elapsed_seconds", 0.0))
        print(f"[LocalLLMClient] ollama done chars={len(text)} elapsed={elapsed:.1f}s")
        return LLMResponse(text=text, model=request.model, elapsed_seconds=elapsed, raw=raw)

    def _chat_completions(self, request: LLMRequest) -> LLMResponse:
        """POST /v1/chat/completions (OpenAI compatible: Ollama, MLX, llama.cpp)."""
        url = f"{self.endpoint}/v1/chat/completions"
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
        if not isinstance(text, str):
            text = str(text)
        elapsed = float(raw.get("_elapsed_seconds", 0.0))
        print(f"[LocalLLMClient] chat done chars={len(text)} elapsed={elapsed:.1f}s")
        return LLMResponse(text=text, model=request.model, elapsed_seconds=elapsed, raw=raw)

    def _post_json(self, url: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """POST JSON and parse object response."""
        body = json.dumps(payload).encode("utf-8")
        print(f"[LocalLLMClient] POST {url} bytes={len(body)}")
        req = urllib.request.Request(
            url,
            data=body,
            headers={"Content-Type": "application/json"},
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
                f"LLM unreachable at {url}. Is Ollama or your local server running?"
            ) from exc
        elapsed = time.time() - started
        print(f"[LocalLLMClient] response bytes={len(raw_bytes)} elapsed={elapsed:.1f}s")
        data = json.loads(raw_bytes.decode("utf-8"))
        if not isinstance(data, dict):
            raise RuntimeError(f"LLM returned non object JSON from {url}")
        data["_elapsed_seconds"] = elapsed
        return data
