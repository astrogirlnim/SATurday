"""
Configuration system for SATurday.

Provides:
- Pydantic schemas for type-safe configuration
- Config loader with override support (file -> env -> CLI)
- Validation with helpful error messages
"""

from infra.config.schemas import SaturdayConfig
from infra.config.loader import load_config, ConfigLoader

__all__ = [
    "SaturdayConfig",
    "load_config",
    "ConfigLoader",
]

