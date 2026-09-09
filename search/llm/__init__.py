"""
Shared local LLM client for SATurday.

All research loop and legacy agent LLM calls should go through LocalLLMClient
so the repo stays on localhost OpenAI compatible or Ollama endpoints only.
"""

from search.llm.client import LocalLLMClient, LLMRequest, LLMResponse

__all__ = [
    "LocalLLMClient",
    "LLMRequest",
    "LLMResponse",
]
