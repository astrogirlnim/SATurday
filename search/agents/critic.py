"""
Proof Critic Agent - Barrier-aware analysis using heuristic detection.

This agent:
- Analyzes Lean proofs for known complexity-theoretic barriers
- Detects relativization barrier signals
- Detects natural proof barrier signals
- Performs oracle diagnostics
- Provides actionable suggestions for improvement

## Architecture
- ProofParser: Extracts structure from Lean theorem files
- BarrierDetector: Applies heuristic checks for barriers
- CriticAgent: Orchestrates analysis and generates reports

## Barrier Detection
1. Relativization: Checks if proof uses oracle-independent techniques
2. Natural Proofs: Checks for largeness + constructivity combination
3. Oracle Diagnostics: Conceptually tests proof with different oracles

LOG: Enhanced Proof Critic with heuristic barrier detection
"""

import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from dataclasses import dataclass

from .core import AgentBase, AgentContext, AgentResult


@dataclass
class ProofAnalysis:
    """
    Complete barrier analysis for a single proof.
    
    Attributes:
        theorem_name: Name of the theorem
        theorem_file: Path to Lean file
        circuit_type: Type of circuit (monotone, AC0, formula, etc.)
        has_sorry: Whether proof uses sorry placeholder
        relativization: Relativization check results
        natural_proofs: Natural proof check results
        oracle_diagnostics: Oracle diagnostic results
        barrier_tags: List of barrier tags (e.g., RELATIVIZING, NON_RELATIVIZING)
        overall_assessment: Quality assessment string
    """
    theorem_name: str
    theorem_file: str
    circuit_type: str
    has_sorry: bool
    relativization: Dict[str, Any]
    natural_proofs: Dict[str, Any]
    oracle_diagnostics: Dict[str, Any]
    barrier_tags: List[str]
    overall_assessment: str


class ProofParser:
    """
    Parse Lean theorem files to extract proof structure.
    
    Uses text-based pattern matching to identify:
    - Theorem names and statements
    - Tactics used in proofs
    - Lemmas referenced
    - Circuit-specific properties
    - Presence of sorry placeholders
    """
    
    def parse_lean_file(self, filepath: Path) -> Dict[str, Any]:
        """
        Extract proof structure from Lean file.
        
        Args:
            filepath: Path to .lean file
            
        Returns:
            Dictionary with extracted proof data:
            - theorem_name: Name of main theorem
            - tactics: List of tactics used
            - lemmas_used: List of lemmas referenced
            - circuit_properties: Circuit-specific keywords found
            - has_sorry: Whether proof uses sorry
            - imports: List of imported modules
            - content: Full file content
        """
        if not filepath.exists():
            print(f"LOG [ProofParser]: File not found: {filepath}", file=sys.stderr)
            return self._empty_parse_result(str(filepath))
        
        with open(filepath, 'r') as f:
            content = f.read()
        
        return {
            "theorem_name": self._extract_theorem_name(content),
            "tactics": self._extract_tactics(content),
            "lemmas_used": self._extract_lemmas(content),
            "circuit_properties": self._extract_circuit_properties(content),
            "has_sorry": "sorry" in content,
            "imports": self._extract_imports(content),
            "content": content,
        }
    
    def _empty_parse_result(self, filepath: str) -> Dict[str, Any]:
        """Return empty parse result for missing files."""
        return {
            "theorem_name": "unknown",
            "tactics": [],
            "lemmas_used": [],
            "circuit_properties": [],
            "has_sorry": True,
            "imports": [],
            "content": "",
        }
    
    def _extract_theorem_name(self, content: str) -> str:
        """Extract theorem name from content."""
        # Pattern: theorem <name> ...
        match = re.search(r'theorem\s+(\w+)', content)
        if match:
            return match.group(1)
        return "unknown"
    
    def _extract_tactics(self, content: str) -> List[str]:
        """Extract tactics used in proof."""
        tactics = []
        
        # Common Lean 4 tactics
        tactic_patterns = [
            'induction', 'cases', 'simp', 'omega', 'ring', 'exact',
            'apply', 'rw', 'unfold', 'intro', 'intros', 'have',
            'interval_cases', 'split', 'constructor', 'assumption',
            'rfl', 'trivial', 'contradiction', 'exfalso',
        ]
        
        for tactic in tactic_patterns:
            if re.search(rf'\b{tactic}\b', content):
                tactics.append(tactic)
        
        return tactics
    
    def _extract_lemmas(self, content: str) -> List[str]:
        """Extract lemmas referenced in proof."""
        lemmas = []
        
        # Pattern: apply <lemma>, exact <lemma>, etc.
        lemma_calls = re.findall(r'(?:apply|exact|rw)\s+(\w+(?:\.\w+)*)', content)
        lemmas.extend(lemma_calls)
        
        return list(set(lemmas))  # Remove duplicates
    
    def _extract_circuit_properties(self, content: str) -> List[str]:
        """Extract circuit-specific keywords and properties."""
        properties = []
        
        # Circuit types and properties
        circuit_keywords = [
            'monotone', 'AC0', 'formula', 'depth', 'size', 'gates',
            'fan_in', 'fan_out', 'parity', 'majority', 'threshold',
            'circuit', 'exponential', 'polynomial', 'linear',
            'lower_bound', 'upper_bound',
        ]
        
        for keyword in circuit_keywords:
            if re.search(rf'\b{keyword}\b', content, re.IGNORECASE):
                properties.append(keyword.lower())
        
        return list(set(properties))
    
    def _extract_imports(self, content: str) -> List[str]:
        """Extract imported modules."""
        imports = []
        
        # Pattern: import <module>
        import_matches = re.findall(r'import\s+([\w.]+)', content)
        imports.extend(import_matches)
        
        return imports


class BarrierDetector:
    """
    Heuristic analyzer for complexity-theoretic barriers.
    
    Implements detection for:
    1. Relativization barrier
    2. Natural proofs barrier
    3. Oracle diagnostics
    
    All checks are heuristic-based and provide confidence scores.
    """
    
    def check_relativization(self, proof_data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Detect relativization barrier signals.
        
        Heuristics:
        - Does proof use oracle-independent operations?
        - Does proof use diagonalization without oracle queries?
        - Does proof use only local circuit properties?
        
        Args:
            proof_data: Parsed proof structure
            
        Returns:
            Dictionary with:
            - relativizes: bool (likely relativizes)
            - confidence: float (0.0-1.0)
            - evidence: List[str] (supporting evidence)
            - suggestions: List[str] (improvement suggestions)
        """
        evidence = []
        score = 0.0  # Higher = more likely to relativize
        
        # Heuristic 1: Check for oracle/blackbox operations
        # Presence of oracle suggests oracle-dependent proof (good!)
        if "oracle" in proof_data["content"].lower() or "blackbox" in proof_data["content"].lower():
            score -= 0.3  # Less likely to relativize
            evidence.append("Uses oracle/blackbox operations (non-relativizing signal)")
        else:
            score += 0.2
            evidence.append("No explicit oracle operations found")
        
        # Heuristic 2: Check for diagonalization
        if "diag" in proof_data["content"].lower():
            if "oracle" not in proof_data["content"].lower():
                score += 0.4
                evidence.append("Uses diagonalization without oracle queries (relativizing signal)")
            else:
                score -= 0.2
                evidence.append("Uses oracle-based diagonalization (non-relativizing signal)")
        
        # Heuristic 3: Check for local circuit properties
        # Local properties (size, depth, monotone) are oracle-independent
        local_props = ["monotone", "depth", "size", "gates", "fan_in"]
        local_count = sum(1 for prop in local_props if prop in proof_data["circuit_properties"])
        
        if local_count >= 2:
            score += 0.3
            evidence.append(f"Uses {local_count} local circuit properties (may relativize)")
        
        # Heuristic 4: Check for arithmetization techniques
        # Arithmetization is a non-relativizing technique
        arith_keywords = ["arithmetiz", "algebraic", "polynomial_evaluation", "multilinear"]
        if any(kw in proof_data["content"].lower() for kw in arith_keywords):
            score -= 0.4
            evidence.append("Uses arithmetization techniques (non-relativizing)")
        
        # Heuristic 5: Check for interactive proof gadgets
        ip_keywords = ["interactive", "prover", "verifier", "protocol"]
        if any(kw in proof_data["content"].lower() for kw in ip_keywords):
            score -= 0.3
            evidence.append("Uses interactive proof techniques (non-relativizing)")
        
        # Normalize score to 0-1 range
        confidence = max(0.0, min(1.0, score))
        relativizes = confidence > 0.5
        
        suggestions = []
        if relativizes:
            suggestions.append("Consider using arithmetization techniques (e.g., low-degree polynomials)")
            suggestions.append("Try interactive proof gadgets (IP, PCP constructions)")
            suggestions.append("Look for non-uniform circuit arguments with advice")
            suggestions.append("Explore algebraic circuit models")
        else:
            suggestions.append("Good! Proof shows non-relativizing signals")
            suggestions.append("Document which oracle-dependent techniques are used")
        
        return {
            "relativizes": relativizes,
            "confidence": confidence,
            "evidence": evidence,
            "suggestions": suggestions,
        }
    
    def check_natural_proofs(
        self,
        proof_data: Dict[str, Any],
        circuit_type: str
    ) -> Dict[str, Any]:
        """
        Detect natural proof barrier signals.
        
        Natural proofs (Razborov-Rudich) have two properties:
        1. Largeness: Applies to large fraction of functions
        2. Constructivity: Bound is efficiently computable
        
        Combination of both may violate cryptographic assumptions.
        
        Args:
            proof_data: Parsed proof structure
            circuit_type: Type of circuit being analyzed
            
        Returns:
            Dictionary with:
            - is_natural_proof: bool
            - largeness_score: float (0.0-1.0)
            - constructivity_score: float (0.0-1.0)
            - evidence: List[str]
            - suggestions: List[str]
        """
        evidence = []
        largeness_score = 0.0
        constructivity_score = 0.0
        
        # === LARGENESS CHECK ===
        # Checks if proof applies to broad class of functions
        
        # Check for broad quantifiers
        broad_quantifiers = [r'∀', r'forall', r'∀.*circuit']
        for q in broad_quantifiers:
            if re.search(q, proof_data["content"]):
                largeness_score += 0.3
                evidence.append("Uses universal quantification over circuits")
                break
        
        # Check if applies to large circuit class
        if circuit_type in ["monotone", "AC0", "formula"]:
            largeness_score += 0.3
            evidence.append(f"Applies to broad circuit class: {circuit_type}")
        
        # Check for generic properties (not function-specific)
        generic_props = ["all", "any", "every", "general"]
        if any(prop in proof_data["content"].lower() for prop in generic_props):
            largeness_score += 0.2
            evidence.append("Uses generic/non-specific arguments")
        
        # === CONSTRUCTIVITY CHECK ===
        # Checks if bound is efficiently computable
        
        # Check for explicit construction
        if "explicit" in proof_data["content"].lower():
            constructivity_score += 0.4
            evidence.append("Uses explicit construction")
        
        # Check for counting arguments
        counting_keywords = ["count", "cardinality", "enumerate", "sum"]
        if any(kw in proof_data["content"].lower() for kw in counting_keywords):
            constructivity_score += 0.4
            evidence.append("Uses counting/enumeration arguments")
        
        # Check for polynomial-time computability
        poly_keywords = ["polynomial", "efficient", "computable"]
        if any(kw in proof_data["content"].lower() for kw in poly_keywords):
            constructivity_score += 0.3
            evidence.append("Bound appears polynomial-time computable")
        
        # Check tactics used
        if "simp" in proof_data["tactics"] or "omega" in proof_data["tactics"]:
            constructivity_score += 0.2
            evidence.append("Uses decidable/computable tactics")
        
        # Natural proof if both largeness and constructivity are high
        is_natural_proof = (largeness_score > 0.5 and constructivity_score > 0.5)
        
        suggestions = []
        if is_natural_proof:
            suggestions.append("WARNING: May conflict with cryptographic hardness assumptions")
            suggestions.append("Consider restricting to non-uniform circuits (advice)")
            suggestions.append("Check if bound is PRG-compatible")
            suggestions.append("Verify method doesn't break one-way functions")
        else:
            if largeness_score > 0.5:
                suggestions.append("Proof is large (applies broadly), but not fully constructive")
            if constructivity_score > 0.5:
                suggestions.append("Proof is constructive, but not overly broad")
        
        return {
            "is_natural_proof": is_natural_proof,
            "largeness_score": largeness_score,
            "constructivity_score": constructivity_score,
            "evidence": evidence,
            "suggestions": suggestions,
        }
    
    def oracle_diagnostics(self, proof_data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Perform conceptual oracle diagnostic.
        
        Asks: "Would this proof work with a PSPACE-complete oracle?"
        If proof fails with hard oracle, that's a good sign (non-relativizing).
        
        Args:
            proof_data: Parsed proof structure
            
        Returns:
            Dictionary with:
            - core_technique: str (identified proof technique)
            - oracle_dependent: bool
            - would_fail_with_hard_oracle: bool (good sign!)
            - interpretation: str (explanation)
        """
        # Identify core proof technique
        core_technique = self._identify_technique(proof_data)
        
        # Check if proof mentions oracles explicitly
        oracle_dependent = (
            "oracle" in proof_data["content"].lower() or
            "query" in proof_data["content"].lower() or
            "blackbox" in proof_data["content"].lower()
        )
        
        # Heuristic: Non-oracle-dependent proofs likely work with any oracle
        # Oracle-dependent proofs may fail with hard oracle (good!)
        would_fail_with_hard_oracle = oracle_dependent
        
        if oracle_dependent:
            interpretation = (
                "Proof appears to use oracle-specific properties. "
                "This is a POSITIVE signal for non-relativizing techniques. "
                "The proof likely fails or requires different arguments with "
                "a PSPACE-complete oracle, suggesting it circumvents relativization."
            )
        else:
            interpretation = (
                "Proof appears oracle-independent, using only local properties. "
                "This suggests the proof may work identically with any oracle, "
                "which is a relativizing property. Consider adding oracle-specific "
                "arguments or techniques to break relativization barrier."
            )
        
        return {
            "core_technique": core_technique,
            "oracle_dependent": oracle_dependent,
            "would_fail_with_hard_oracle": would_fail_with_hard_oracle,
            "interpretation": interpretation,
        }
    
    def _identify_technique(self, proof_data: Dict[str, Any]) -> str:
        """
        Heuristically identify core proof technique.
        
        Args:
            proof_data: Parsed proof structure
            
        Returns:
            String description of technique
        """
        tactics = proof_data.get("tactics", [])
        content = proof_data.get("content", "").lower()
        
        if "induction" in tactics:
            return "induction"
        elif "cases" in tactics or "interval_cases" in tactics:
            return "case_analysis"
        elif "exponential" in content:
            return "exponential_lower_bound"
        elif "approximation" in content or "razborov" in content:
            return "approximation_method"
        elif "algebraic" in content or "polynomial" in content:
            return "algebraic_techniques"
        elif "counting" in content or "cardinality" in content:
            return "counting_argument"
        else:
            return "unknown"


class CriticAgent(AgentBase):
    """
    Barrier-aware proof critic using heuristic analysis.
    
    Analyzes Lean theorem files for complexity-theoretic barriers:
    1. Relativization barrier detection
    2. Natural proofs barrier detection
    3. Oracle diagnostics
    
    Provides confidence-scored analysis with actionable suggestions.
    """
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        """
        Initialize Critic Agent.
        
        Args:
            config: Optional configuration dictionary
        """
        super().__init__("critic")
        self.config = config or {}
        self.parser = ProofParser()
        self.detector = BarrierDetector()
    
    def plan(self, context: AgentContext) -> Dict[str, Any]:
        """
        Plan barrier analysis strategy.
        
        Args:
            context: Agent execution context
            
        Returns:
            Analysis plan with theorem files and conjectures
        """
        context.log(self.name, "Planning barrier analysis")
        
        # Get theorems from formalizer
        formalizer_artifacts = context.artifacts.get("formalizer", {})
        theorem_files = formalizer_artifacts.get("theorem_files", [])
        
        # Get conjecture metadata from conjecturer
        conjecturer_artifacts = context.artifacts.get("conjecturer", {})
        conjectures = conjecturer_artifacts.get("conjectures", [])
        
        context.log(self.name, f"Received {len(theorem_files)} theorem files to analyze")
        context.log(self.name, f"Received {len(conjectures)} conjecture metadata entries")
        
        analysis_plan = {
            "theorem_files": theorem_files,
            "conjectures": conjectures,
            "checks": [
                "relativization",
                "natural_proofs",
                "oracle_diagnostics",
            ],
        }
        
        return analysis_plan
    
    def act(self, context: AgentContext, plan: Dict[str, Any]) -> AgentResult:
        """
        Execute barrier analysis on theorems.
        
        Args:
            context: Agent execution context
            plan: Analysis plan from plan()
            
        Returns:
            AgentResult with analyses and summary
        """
        context.log(self.name, "Analyzing proofs for complexity-theoretic barriers")
        
        theorem_files = plan.get("theorem_files", [])
        conjectures = plan.get("conjectures", [])
        
        # Build conjecture lookup by ID
        conjecture_map = {}
        for c in conjectures:
            if isinstance(c, dict):
                cid = c.get("conjecture_id", "")
                conjecture_map[cid] = c
        
        context.log(self.name, f"Built conjecture map with {len(conjecture_map)} entries")
        
        analyses = []
        for theorem_file in theorem_files:
            context.log(self.name, f"Analyzing {theorem_file}")
            
            # Parse proof structure
            proof_data = self.parser.parse_lean_file(Path(theorem_file))
            
            # Get associated conjecture metadata
            theorem_name = proof_data["theorem_name"]
            conjecture_id = self._extract_conjecture_id(theorem_name)
            conjecture = conjecture_map.get(conjecture_id, {})
            circuit_type = conjecture.get("circuit_type", "unknown")
            
            context.log(self.name, f"  Theorem: {theorem_name}")
            context.log(self.name, f"  Circuit type: {circuit_type}")
            context.log(self.name, f"  Has sorry: {proof_data['has_sorry']}")
            
            # Run barrier checks
            rel_check = self.detector.check_relativization(proof_data)
            nat_check = self.detector.check_natural_proofs(proof_data, circuit_type)
            oracle_diag = self.detector.oracle_diagnostics(proof_data)
            
            # Compile analysis
            analysis = ProofAnalysis(
                theorem_name=theorem_name,
                theorem_file=str(theorem_file),
                circuit_type=circuit_type,
                has_sorry=proof_data["has_sorry"],
                relativization=rel_check,
                natural_proofs=nat_check,
                oracle_diagnostics=oracle_diag,
                barrier_tags=self._compile_tags(rel_check, nat_check, oracle_diag),
                overall_assessment=self._assess_proof_quality(rel_check, nat_check, oracle_diag),
            )
            
            analyses.append(analysis)
            
            # Log key findings
            self._log_findings(context, analysis)
        
        # Generate summary statistics
        summary = self._generate_summary(analyses)
        
        context.log(self.name, f"Analysis complete: {len(analyses)} proofs analyzed")
        context.log(self.name, f"  Relativizing: {summary['relativizing_count']}")
        context.log(self.name, f"  Non-relativizing: {summary['non_relativizing_count']}")
        context.log(self.name, f"  Natural proof concerns: {summary['natural_proof_count']}")
        
        # Convert analyses to dictionaries for serialization
        analyses_dicts = [self._analysis_to_dict(a) for a in analyses]
        
        artifacts = {
            "analyses": analyses_dicts,
            "summary": summary,
        }
        
        metrics = {
            "theorems_analyzed": len(analyses),
            "relativizing": summary["relativizing_count"],
            "non_relativizing": summary["non_relativizing_count"],
            "natural_proof_violations": summary["natural_proof_count"],
            "clean_proofs": summary["clean_count"],
        }
        
        return AgentResult(
            agent_name=self.name,
            status="success",
            artifacts=artifacts,
            metrics=metrics,
        )
    
    def report(self, context: AgentContext, result: AgentResult) -> str:
        """
        Generate Markdown report for barrier analysis.
        
        Args:
            context: Agent execution context
            result: Result from act()
            
        Returns:
            Markdown-formatted report string
        """
        analyses = result.artifacts.get("analyses", [])
        summary = result.artifacts.get("summary", {})
        
        report = f"""# Proof Critic Report

## Executive Summary
- **Theorems Analyzed**: {summary.get('total_analyzed', 0)}
- **Relativizing Proofs**: {summary.get('relativizing_count', 0)}
- **Non-Relativizing Proofs**: {summary.get('non_relativizing_count', 0)}
- **Natural Proof Concerns**: {summary.get('natural_proof_count', 0)}
- **Clean Proofs (No Barriers)**: {summary.get('clean_count', 0)}
- **Status**: {result.status}

## Key Findings

"""
        
        if summary.get('non_relativizing_count', 0) > 0:
            report += "- Excellent: Some proofs show non-relativizing signals!\n"
        if summary.get('clean_count', 0) > 0:
            report += f"- {summary['clean_count']} proofs avoid both relativization and natural proof barriers\n"
        if summary.get('natural_proof_count', 0) > 0:
            report += f"- Warning: {summary['natural_proof_count']} proofs may hit natural proof barrier\n"
        
        report += "\n## Detailed Analysis\n"
        
        for analysis in analyses:
            report += f"\n### {analysis['theorem_name']}\n"
            report += f"- **File**: `{analysis['theorem_file']}`\n"
            report += f"- **Circuit Type**: {analysis['circuit_type']}\n"
            report += f"- **Has Sorry**: {analysis['has_sorry']}\n"
            report += f"- **Barrier Tags**: {', '.join(analysis['barrier_tags'])}\n"
            report += f"- **Overall Assessment**: {analysis['overall_assessment']}\n"
            
            # Relativization details
            rel = analysis['relativization']
            report += f"\n#### Relativization Analysis\n"
            report += f"- **Relativizes**: {rel['relativizes']}\n"
            report += f"- **Confidence**: {rel['confidence']:.2f}\n"
            report += f"- **Evidence**:\n"
            for evidence in rel['evidence']:
                report += f"  - {evidence}\n"
            if rel['suggestions']:
                report += f"- **Suggestions**:\n"
                for suggestion in rel['suggestions']:
                    report += f"  - {suggestion}\n"
            
            # Natural proofs details
            nat = analysis['natural_proofs']
            report += f"\n#### Natural Proofs Analysis\n"
            report += f"- **Is Natural Proof**: {nat['is_natural_proof']}\n"
            report += f"- **Largeness Score**: {nat['largeness_score']:.2f}\n"
            report += f"- **Constructivity Score**: {nat['constructivity_score']:.2f}\n"
            report += f"- **Evidence**:\n"
            for evidence in nat['evidence']:
                report += f"  - {evidence}\n"
            if nat['suggestions']:
                report += f"- **Suggestions**:\n"
                for suggestion in nat['suggestions']:
                    report += f"  - {suggestion}\n"
            
            # Oracle diagnostics
            oracle = analysis['oracle_diagnostics']
            report += f"\n#### Oracle Diagnostics\n"
            report += f"- **Core Technique**: {oracle['core_technique']}\n"
            report += f"- **Oracle Dependent**: {oracle['oracle_dependent']}\n"
            report += f"- **Would Fail with Hard Oracle**: {oracle['would_fail_with_hard_oracle']}\n"
            report += f"- **Interpretation**: {oracle['interpretation']}\n"
        
        report += "\n## Recommendations\n\n"
        
        if summary.get('relativizing_count', 0) > summary.get('non_relativizing_count', 0):
            report += "- **Priority**: Focus on developing non-relativizing techniques\n"
            report += "- Consider: Arithmetization, interactive proofs, algebraic methods\n"
        
        if summary.get('natural_proof_count', 0) > 0:
            report += "- **Caution**: Some proofs may conflict with crypto assumptions\n"
            report += "- Verify: Bounds are PRG-compatible or restrict to non-uniform circuits\n"
        
        if summary.get('clean_count', 0) > 0:
            report += f"- **Success**: {summary['clean_count']} proofs show promising barrier-free approaches\n"
            report += "- Continue: Develop and extend these techniques\n"
        
        report += "\n## Conclusion\n\n"
        report += "Barrier analysis complete. Non-relativizing proofs and those avoiding natural proof "
        report += "concerns represent the most promising directions for P vs NP research. "
        report += "Focus development on techniques that show oracle-dependent behavior and avoid "
        report += "overly broad or constructive arguments that may conflict with cryptography.\n"
        
        return report
    
    def _extract_conjecture_id(self, theorem_name: str) -> str:
        """
        Extract conjecture ID from theorem name.
        
        Theorem names follow pattern: <circuit>_<function>_n<size>_s<seed>
        or <circuit>_<function>_lower_bound_<size>_s<seed>
        
        Args:
            theorem_name: Theorem name string
            
        Returns:
            Conjecture ID string
        """
        # Remove common suffixes
        name = theorem_name.replace("_lower_bound", "")
        
        # Extract parts: monotone_parity_n2_s12000 -> monotone_parity_n2_s12000
        # Just return the name as-is, assuming it matches conjecture ID format
        return name
    
    def _compile_tags(
        self,
        rel_check: Dict[str, Any],
        nat_check: Dict[str, Any],
        oracle_diag: Dict[str, Any]
    ) -> List[str]:
        """
        Generate barrier tags from check results.
        
        Args:
            rel_check: Relativization check results
            nat_check: Natural proof check results
            oracle_diag: Oracle diagnostic results
            
        Returns:
            List of barrier tag strings
        """
        tags = []
        
        if rel_check["relativizes"]:
            tags.append("RELATIVIZING")
        else:
            tags.append("NON_RELATIVIZING")
        
        if nat_check["is_natural_proof"]:
            tags.append("NATURAL_PROOF")
        
        if oracle_diag.get("would_fail_with_hard_oracle"):
            tags.append("ORACLE_INDEPENDENT")
        
        if oracle_diag.get("core_technique") == "algebraic_techniques":
            tags.append("ALGEBRAIC")
        
        return tags
    
    def _assess_proof_quality(
        self,
        rel_check: Dict[str, Any],
        nat_check: Dict[str, Any],
        oracle_diag: Dict[str, Any]
    ) -> str:
        """
        Generate overall quality assessment.
        
        Args:
            rel_check: Relativization check results
            nat_check: Natural proof check results
            oracle_diag: Oracle diagnostic results
            
        Returns:
            Assessment string
        """
        non_rel = not rel_check["relativizes"]
        no_nat_proof = not nat_check["is_natural_proof"]
        
        if non_rel and no_nat_proof:
            return "EXCELLENT: Non-relativizing and avoids natural proof barrier"
        elif non_rel:
            return "GOOD: Non-relativizing (but check natural proof concerns)"
        elif no_nat_proof:
            return "MODERATE: Avoids natural proofs but may relativize"
        else:
            return "CAUTION: May encounter multiple complexity-theoretic barriers"
    
    def _log_findings(self, context: AgentContext, analysis: ProofAnalysis) -> None:
        """
        Log key findings from analysis.
        
        Args:
            context: Agent execution context
            analysis: Proof analysis results
        """
        if "NON_RELATIVIZING" in analysis.barrier_tags:
            context.log(self.name, f"  GOOD: {analysis.theorem_name} shows non-relativizing signals", "INFO")
        
        if "NATURAL_PROOF" in analysis.barrier_tags:
            context.log(self.name, f"  WARNING: {analysis.theorem_name} may hit natural proof barrier", "WARN")
        
        if "ORACLE_INDEPENDENT" in analysis.barrier_tags:
            context.log(self.name, f"  EXCELLENT: {analysis.theorem_name} is oracle-dependent (non-relativizing)", "INFO")
    
    def _generate_summary(self, analyses: List[ProofAnalysis]) -> Dict[str, Any]:
        """
        Generate summary statistics from analyses.
        
        Args:
            analyses: List of proof analyses
            
        Returns:
            Summary dictionary
        """
        total = len(analyses)
        relativizing = sum(1 for a in analyses if a.relativization["relativizes"])
        non_relativizing = total - relativizing
        natural_proof = sum(1 for a in analyses if a.natural_proofs["is_natural_proof"])
        clean = sum(1 for a in analyses 
                   if not a.relativization["relativizes"] 
                   and not a.natural_proofs["is_natural_proof"])
        
        return {
            "total_analyzed": total,
            "relativizing_count": relativizing,
            "non_relativizing_count": non_relativizing,
            "natural_proof_count": natural_proof,
            "clean_count": clean,
        }
    
    def _analysis_to_dict(self, analysis: ProofAnalysis) -> Dict[str, Any]:
        """
        Convert ProofAnalysis to dictionary for serialization.
        
        Args:
            analysis: ProofAnalysis object
            
        Returns:
            Dictionary representation
        """
        return {
            "theorem_name": analysis.theorem_name,
            "theorem_file": analysis.theorem_file,
            "circuit_type": analysis.circuit_type,
            "has_sorry": analysis.has_sorry,
            "relativization": analysis.relativization,
            "natural_proofs": analysis.natural_proofs,
            "oracle_diagnostics": analysis.oracle_diagnostics,
            "barrier_tags": analysis.barrier_tags,
            "overall_assessment": analysis.overall_assessment,
        }
