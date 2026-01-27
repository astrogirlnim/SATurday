"""
Base classes for conjecture template system.

Provides abstract ConjectureTemplate class and Conjecture dataclass.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Dict, Optional
from pathlib import Path
import yaml


@dataclass
class Conjecture:
    """
    A generated conjecture instance.
    
    Attributes:
        conjecture_id: Unique identifier for this conjecture
        task_id: ID of the task that generated this conjecture
        bet: Research bet (A, B, C, or D)
        lean_stub: Lean theorem with sorry placeholder
        cnf_spec: CNF specification parameters
        metadata: Additional information about generation
        lean_file_path: Path where Lean stub will be written
        spec_file_path: Path where CNF spec will be written
    """
    conjecture_id: str
    task_id: str
    bet: str
    lean_stub: str
    cnf_spec: Dict[str, Any]
    metadata: Dict[str, Any] = field(default_factory=dict)
    lean_file_path: Optional[Path] = None
    spec_file_path: Optional[Path] = None
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert conjecture to dictionary for serialization."""
        return {
            "conjecture_id": self.conjecture_id,
            "task_id": self.task_id,
            "bet": self.bet,
            "lean_stub_preview": self.lean_stub[:200] + "..." if len(self.lean_stub) > 200 else self.lean_stub,
            "cnf_spec": self.cnf_spec,
            "metadata": self.metadata,
            "lean_file": str(self.lean_file_path) if self.lean_file_path else None,
            "spec_file": str(self.spec_file_path) if self.spec_file_path else None,
        }
    
    def write_lean_stub(self, base_dir: Path) -> Path:
        """
        Write Lean stub to file.
        
        Args:
            base_dir: Base directory for Lean files (e.g., theory/Conjectures)
        
        Returns:
            Path to written file
        """
        # Determine subdirectory based on bet
        bet_dir = base_dir / f"Bet{self.bet}"
        bet_dir.mkdir(parents=True, exist_ok=True)
        
        # Generate filename from conjecture ID
        filename = f"{self.conjecture_id}.lean"
        file_path = bet_dir / filename
        
        print(f"[Conjecture] Writing Lean stub to {file_path}")
        
        # Write Lean content
        with open(file_path, 'w') as f:
            f.write(self.lean_stub)
        
        self.lean_file_path = file_path
        return file_path
    
    def write_cnf_spec(self, base_dir: Path) -> Path:
        """
        Write CNF specification to YAML file.
        
        Args:
            base_dir: Base directory for specs (e.g., search/specs)
        
        Returns:
            Path to written file
        """
        base_dir.mkdir(parents=True, exist_ok=True)
        
        # Generate filename from conjecture ID
        filename = f"{self.conjecture_id}.yaml"
        file_path = base_dir / filename
        
        print(f"[Conjecture] Writing CNF spec to {file_path}")
        
        # Write YAML content
        with open(file_path, 'w') as f:
            yaml.dump(self.cnf_spec, f, default_flow_style=False, sort_keys=False)
        
        self.spec_file_path = file_path
        return file_path


class ConjectureTemplate(ABC):
    """
    Abstract base class for conjecture templates.
    
    Each template generates:
    1. A Lean theorem stub with sorry placeholder
    2. A CNF specification for SAT mining
    
    Templates are bet-specific and parameterized by task details.
    """
    
    def __init__(self, template_id: str, bet: str):
        """
        Initialize template.
        
        Args:
            template_id: Unique identifier for this template type
            bet: Research bet (A, B, C, or D)
        """
        self.template_id = template_id
        self.bet = bet
        print(f"[Template] Initialized {template_id} for Bet {bet}")
    
    @abstractmethod
    def generate_lean_stub(self, **params) -> str:
        """
        Generate Lean theorem stub.
        
        Args:
            **params: Template-specific parameters (e.g., n, seed, circuit_type)
        
        Returns:
            Lean code string with theorem and sorry placeholder
        """
        pass
    
    @abstractmethod
    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        """
        Generate CNF specification.
        
        Args:
            **params: Template-specific parameters
        
        Returns:
            Dictionary with CNF generation parameters
        """
        pass
    
    def instantiate(self, task: Dict[str, Any]) -> Conjecture:
        """
        Instantiate template with task parameters.
        
        Args:
            task: Task dictionary from planner
        
        Returns:
            Conjecture instance
        """
        print(f"[Template] Instantiating {self.template_id} for task {task.get('task_id')}")
        
        # Extract parameters from task
        task_id = task.get("task_id", "unknown")
        problem_size = task.get("problem_size", 2)
        seed = task.get("seed", 0)
        circuit_type = task.get("circuit_type")
        
        # Generate conjecture ID
        conjecture_id = f"{self.template_id}_n{problem_size}_s{seed}"
        
        # Generate Lean stub and CNF spec
        lean_stub = self.generate_lean_stub(
            n=problem_size,
            seed=seed,
            circuit_type=circuit_type,
            task_id=task_id,
        )
        
        cnf_spec = self.generate_cnf_spec(
            n=problem_size,
            seed=seed,
            circuit_type=circuit_type,
            task_id=task_id,
        )
        
        # Create conjecture
        conjecture = Conjecture(
            conjecture_id=conjecture_id,
            task_id=task_id,
            bet=self.bet,
            lean_stub=lean_stub,
            cnf_spec=cnf_spec,
            metadata={
                "template_id": self.template_id,
                "problem_size": problem_size,
                "seed": seed,
                "circuit_type": circuit_type,
            },
        )
        
        print(f"[Template] Created conjecture: {conjecture_id}")
        
        return conjecture


class TemplateRegistry:
    """
    Registry for conjecture templates.
    
    Maps (bet, circuit_type, function_name) -> template.
    """
    
    def __init__(self):
        """Initialize empty registry."""
        self.templates: Dict[tuple, ConjectureTemplate] = {}
        print("[TemplateRegistry] Initialized")
    
    def register(self, bet: str, circuit_type: str, function_name: str, template: ConjectureTemplate):
        """
        Register a template.
        
        Args:
            bet: Research bet (A, B, C, D)
            circuit_type: Circuit type (monotone, ac0, formula, etc.)
            function_name: Target function (parity, majority, threshold, etc.)
            template: Template instance
        """
        key = (bet, circuit_type, function_name)
        self.templates[key] = template
        print(f"[TemplateRegistry] Registered {template.template_id} for ({bet}, {circuit_type}, {function_name})")
    
    def get_template(self, bet: str, circuit_type: str, function_name: str) -> Optional[ConjectureTemplate]:
        """
        Get template for a bet, circuit type, and function.
        
        Args:
            bet: Research bet
            circuit_type: Circuit type
            function_name: Target function name
        
        Returns:
            Template if found, None otherwise
        """
        key = (bet, circuit_type, function_name)
        template = self.templates.get(key)
        if template:
            print(f"[TemplateRegistry] Found template for ({bet}, {circuit_type}, {function_name})")
        else:
            print(f"[TemplateRegistry] No template for ({bet}, {circuit_type}, {function_name})")
        return template
    
    def get_templates_for_circuit(self, bet: str, circuit_type: str) -> list:
        """
        Get all templates for a bet and circuit type (all functions).
        
        Args:
            bet: Research bet
            circuit_type: Circuit type
        
        Returns:
            List of templates
        """
        templates = [
            template for key, template in self.templates.items()
            if key[0] == bet and key[1] == circuit_type
        ]
        print(f"[TemplateRegistry] Found {len(templates)} templates for ({bet}, {circuit_type})")
        return templates
    
    def get_all_templates(self) -> Dict[tuple, ConjectureTemplate]:
        """Get all registered templates."""
        return self.templates
