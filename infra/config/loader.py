"""
Configuration loader with multi-source support.

Load order (later sources override earlier):
1. Default values (from schemas)
2. YAML config file
3. Environment variables
4. CLI arguments (passed as dict)

Environment variable format:
    SATURDAY_<SECTION>_<KEY>=value
    Example: SATURDAY_SOLVER_DEFAULT_SEED=100
"""

import os
import yaml
from pathlib import Path
from typing import Any, Dict, Optional
from pydantic import ValidationError

from infra.config.schemas import SaturdayConfig


class ConfigLoader:
    """
    Configuration loader with override support.
    
    Loads configuration from multiple sources with precedence:
    1. defaults.yaml
    2. Custom config file (if provided)
    3. Environment variables
    4. CLI overrides (if provided)
    """
    
    def __init__(self, repo_root: Optional[Path] = None):
        """
        Initialize config loader.
        
        Args:
            repo_root: Repository root directory (auto-detected if None)
        """
        if repo_root is None:
            # Auto-detect repo root (look for .git directory)
            current = Path(__file__).resolve()
            for parent in [current] + list(current.parents):
                if (parent / ".git").exists():
                    repo_root = parent
                    break
            
            if repo_root is None:
                # Fallback: assume we're in infra/config/
                repo_root = Path(__file__).parent.parent.parent
        
        self.repo_root = Path(repo_root)
        self.config_dir = self.repo_root / "infra" / "config"
        self.defaults_path = self.config_dir / "defaults.yaml"
        
        print(f"[ConfigLoader] Repo root: {self.repo_root}")
        print(f"[ConfigLoader] Config dir: {self.config_dir}")
    
    def load_yaml(self, yaml_path: Path) -> Dict[str, Any]:
        """
        Load configuration from YAML file.
        
        Args:
            yaml_path: Path to YAML file
            
        Returns:
            Configuration dictionary
            
        Raises:
            FileNotFoundError: If file doesn't exist
            yaml.YAMLError: If YAML is invalid
        """
        print(f"[ConfigLoader] Loading YAML from {yaml_path}")
        
        if not yaml_path.exists():
            raise FileNotFoundError(f"Config file not found: {yaml_path}")
        
        with open(yaml_path, "r") as f:
            data = yaml.safe_load(f)
        
        if data is None:
            data = {}
        
        print(f"[ConfigLoader] Loaded {len(data)} top-level keys from YAML")
        
        return data
    
    def load_env_vars(self) -> Dict[str, Any]:
        """
        Load configuration overrides from environment variables.
        
        Environment variables follow the pattern:
            SATURDAY_<SECTION>_<KEY>=value
        
        Example:
            SATURDAY_SOLVER_DEFAULT_SEED=100
            -> {"solver": {"default_seed": 100}}
        
        Returns:
            Configuration overrides dictionary
        """
        print(f"[ConfigLoader] Loading environment variable overrides")
        
        overrides: Dict[str, Any] = {}
        prefix = "SATURDAY_"
        
        for key, value in os.environ.items():
            if not key.startswith(prefix):
                continue
            
            # Remove prefix and convert to lowercase
            remainder = key[len(prefix):].lower()
            
            # Split by underscore, but handle special keys that have underscores
            # Strategy: split on single underscores that aren't part of compound keys
            parts = []
            current_part = []
            
            tokens = remainder.split("_")
            i = 0
            while i < len(tokens):
                token = tokens[i]
                
                # Check if this starts a compound key (look ahead)
                if i + 1 < len(tokens):
                    # Try as compound key first
                    compound = f"{token}_{tokens[i+1]}"
                    # If we've accumulated parts, add the compound
                    if len(current_part) > 0:
                        parts.append("_".join(current_part))
                        current_part = []
                    parts.append(token)
                    i += 1
                else:
                    parts.append(token)
                    i += 1
            
            if len(parts) < 2:
                print(f"[ConfigLoader] WARNING: Invalid env var format: {key}")
                continue
            
            # Build nested dictionary
            current = overrides
            for part in parts[:-1]:
                if part not in current:
                    current[part] = {}
                current = current[part]
            
            # Set value (try to parse as int/float/bool)
            final_key = parts[-1]
            parsed_value = self._parse_value(value)
            current[final_key] = parsed_value
            
            print(f"[ConfigLoader] Env override: {'.'.join(parts)} = {parsed_value}")
        
        return overrides
    
    def _parse_value(self, value: str) -> Any:
        """
        Parse string value to appropriate type.
        
        Args:
            value: String value from environment
            
        Returns:
            Parsed value (int, float, bool, or str)
        """
        # Try boolean
        if value.lower() in ("true", "yes", "1"):
            return True
        if value.lower() in ("false", "no", "0"):
            return False
        
        # Try integer
        try:
            return int(value)
        except ValueError:
            pass
        
        # Try float
        try:
            return float(value)
        except ValueError:
            pass
        
        # Return as string
        return value
    
    def merge_configs(self, base: Dict[str, Any], override: Dict[str, Any]) -> Dict[str, Any]:
        """
        Deep merge two configuration dictionaries.
        
        Override values take precedence over base values.
        
        Args:
            base: Base configuration
            override: Override configuration
            
        Returns:
            Merged configuration
        """
        result = base.copy()
        
        for key, value in override.items():
            if key in result and isinstance(result[key], dict) and isinstance(value, dict):
                # Recursively merge nested dicts
                result[key] = self.merge_configs(result[key], value)
            else:
                # Override value
                result[key] = value
        
        return result
    
    def load(
        self,
        config_file: Optional[Path] = None,
        overrides: Optional[Dict[str, Any]] = None,
        load_env: bool = True,
    ) -> SaturdayConfig:
        """
        Load configuration with all sources.
        
        Load order:
        1. defaults.yaml
        2. Custom config file (if provided)
        3. Environment variables (if load_env=True)
        4. CLI overrides (if provided)
        
        Args:
            config_file: Optional custom config file
            overrides: Optional override dictionary (from CLI)
            load_env: Whether to load environment variables
            
        Returns:
            Validated SaturdayConfig object
            
        Raises:
            ValidationError: If configuration is invalid
            FileNotFoundError: If config file not found
        """
        print(f"[ConfigLoader] Loading configuration")
        print(f"[ConfigLoader]   Defaults: {self.defaults_path}")
        if config_file:
            print(f"[ConfigLoader]   Custom config: {config_file}")
        print(f"[ConfigLoader]   Load env vars: {load_env}")
        if overrides:
            print(f"[ConfigLoader]   CLI overrides: {len(overrides)} keys")
        
        # Start with defaults
        config_dict = self.load_yaml(self.defaults_path)
        
        # Merge custom config file
        if config_file is not None:
            custom_config = self.load_yaml(config_file)
            config_dict = self.merge_configs(config_dict, custom_config)
            print(f"[ConfigLoader] Merged custom config from {config_file}")
        
        # Merge environment variables
        if load_env:
            env_overrides = self.load_env_vars()
            if env_overrides:
                config_dict = self.merge_configs(config_dict, env_overrides)
                print(f"[ConfigLoader] Merged environment variable overrides")
        
        # Merge CLI overrides
        if overrides:
            config_dict = self.merge_configs(config_dict, overrides)
            print(f"[ConfigLoader] Merged CLI overrides")
        
        # Validate with Pydantic
        print(f"[ConfigLoader] Validating configuration with Pydantic")
        
        try:
            config = SaturdayConfig(**config_dict)
            print(f"[ConfigLoader] Configuration validated successfully")
            
            # Validate policies
            config.validate_all_policies()
            
            return config
            
        except ValidationError as e:
            print(f"[ConfigLoader] ERROR: Configuration validation failed")
            print(f"[ConfigLoader] {e}")
            raise
    
    def save(self, config: SaturdayConfig, output_path: Path) -> None:
        """
        Save configuration to YAML file.
        
        Args:
            config: Configuration object
            output_path: Output file path
        """
        print(f"[ConfigLoader] Saving configuration to {output_path}")
        
        # Convert to dict
        config_dict = config.dict()
        
        # Write to YAML
        with open(output_path, "w") as f:
            yaml.dump(config_dict, f, default_flow_style=False, sort_keys=False)
        
        print(f"[ConfigLoader] Configuration saved")


def load_config(
    config_file: Optional[Path] = None,
    overrides: Optional[Dict[str, Any]] = None,
    repo_root: Optional[Path] = None,
) -> SaturdayConfig:
    """
    Convenience function to load configuration.
    
    Args:
        config_file: Optional custom config file
        overrides: Optional override dictionary
        repo_root: Optional repo root (auto-detected if None)
        
    Returns:
        Validated SaturdayConfig object
    """
    loader = ConfigLoader(repo_root=repo_root)
    return loader.load(config_file=config_file, overrides=overrides)

