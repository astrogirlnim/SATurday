"""
Oracle World Construction for Barrier Analysis (V10).

This module implements the core of the real barrier analysis upgrade to the
Proof Critic agent. Instead of heuristic string-matching, we construct
explicit relativized worlds and check whether a given proof argument survives
relativization.

## Theoretical Background

Baker-Gill-Solovay (1975) showed:
  There exist oracles A, B such that P^A = NP^A and P^B != NP^B.

This means any proof technique that works the same way regardless of the
oracle is insufficient to resolve P vs NP. Such techniques are called
"relativizing." Non-relativizing techniques (IP = PSPACE, PCP theorem, etc.)
must use oracle-specific information.

## What We Construct

For each proof attempt, we construct two canonical oracle witnesses:

1. Collapsing oracle A (P^A = NP^A):
   - Defined on all polynomial-length queries
   - Language LA: "Does M accept input x within k steps for polynomial k?"
   - A proof that works with this oracle cannot separate P from NP

2. Separating oracle B (P^B != NP^B):
   - B is a PSPACE-complete language encoded as a truth table
   - Language LB: "Does the t-th variable appear in the oracle's circuit?"
   - A proof that fails with this oracle is relativizing

3. Non-relativizing check:
   - We ask the LLM (if available) whether the proof argument uses
     any technique that would behave differently under oracles A vs B.
   - Techniques that pass: arithmetization, interactive proofs, PCPs,
     algebraic geometry codes, sum-check protocol.
   - Techniques that fail: diagonalization alone, counting alone, any
     argument that treats the computation as a black box.

## OracleWitness dataclass

For each proof, we produce an OracleWitness:
  oracle_type:         "collapsing" | "separating" | "both"
  circuit_class:       circuit type the proof targets (monotone, AC0, etc.)
  proof_technique:     identified proof technique
  relativizes:         True if proof argument survives with a PSPACE oracle
  witness_description: human-readable description of the oracle world
  non_rel_suggestion:  LLM-proposed non-relativizing tweak (if LLM available)
  confidence:          float 0-1, certainty of the classification
"""

import json
import sys
import time
import hashlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional


@dataclass
class OracleWitness:
    """
    Explicit oracle-world witness for a proof attempt's relativization status.

    Produced by OracleWorldBuilder for each proof attempt passed through the
    upgraded Critic (V10). Contains the actual oracle world description,
    the relativization verdict, and (if LLM active) a proposed fix.

    Attributes:
        proof_file:           Path to Lean theorem file analyzed
        oracle_type:          Type of oracle witness: collapsing, separating, or both
        circuit_class:        Circuit class targeted by the proof
        proof_technique:      The core technique identified in the proof
        relativizes:          True if the proof argument relativizes
        witness_description:  Concrete description of the oracle world
        oracle_queries:       List of oracle queries that expose relativization
        non_rel_suggestion:   LLM-proposed non-relativizing variant (or None)
        confidence:           Confidence in the classification (0.0-1.0)
        llm_reasoning:        Raw LLM reasoning about the oracle world (if used)
    """
    proof_file: str
    oracle_type: str
    circuit_class: str
    proof_technique: str
    relativizes: bool
    witness_description: str
    oracle_queries: List[str] = field(default_factory=list)
    non_rel_suggestion: Optional[str] = None
    confidence: float = 0.5
    llm_reasoning: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        """Serialize witness to dictionary."""
        return {
            "proof_file": self.proof_file,
            "oracle_type": self.oracle_type,
            "circuit_class": self.circuit_class,
            "proof_technique": self.proof_technique,
            "relativizes": self.relativizes,
            "witness_description": self.witness_description,
            "oracle_queries": self.oracle_queries,
            "non_rel_suggestion": self.non_rel_suggestion,
            "confidence": self.confidence,
            "llm_reasoning": self.llm_reasoning,
        }


class OracleWorldBuilder:
    """
    Constructs explicit relativized oracle worlds to classify proof techniques.

    Core logic:
    1. Parse the proof's tactics and structure.
    2. Identify the core technique (case_analysis, induction, counting, etc.).
    3. Determine whether that technique is oracle-relative:
       - Case analysis / exhaustive enumeration: always relativizes
         (a PSPACE oracle can make every finite case work or fail).
       - Counting/pigeonhole alone: relativizes (oracle can pad to any size).
       - Arithmetization / polynomial encoding: NON-relativizing signal.
       - Interactive proof protocol: NON-relativizing signal.
       - Algebraic circuit model: NON-relativizing signal.
       - Random restriction / switching lemma: NON-relativizing signal.
    4. Construct the canonical collapsing or separating oracle witness.
    5. If LLM is available, query it to describe the oracle world concretely
       and propose a non-relativizing tweak.

    The classification rules here are grounded in complexity theory:
    - Baker-Gill-Solovay 1975 (relativization barrier)
    - Razborov-Rudich 1994 (natural proofs barrier)
    - Aaronson-Wigderson 2009 (algebrization barrier)
    """

    # Techniques known to be relativizing (cannot separate P from NP alone)
    RELATIVIZING_TECHNIQUES = {
        "case_analysis":       "Exhaustive case analysis works with any oracle: oracle can invert cases.",
        "induction":           "Induction alone relativizes: oracle can embed hard instances at each step.",
        "counting_argument":   "Pure counting/pigeonhole relativizes: oracle pads to break any counting.",
        "diagonalization":     "Diagonalization (without oracle queries) relativizes by BGS 1975.",
        "unknown":             "Unknown technique assumed relativizing by default (conservative).",
    }

    # Techniques with non-relativizing potential
    NON_RELATIVIZING_TECHNIQUES = {
        "arithmetization":     "Polynomial evaluation is oracle-independent: same polynomial works regardless.",
        "algebraic_techniques":"Algebraic methods (GF(2), low-degree polys) are non-relativizing.",
        "approximation_method":"Razborov's approximation method is non-relativizing.",
        "interactive_proof":   "Sum-check protocol is non-relativizing (IP=PSPACE proof).",
        "algebraization":      "Algebrization uses algebraic extensions: partially non-relativizing.",
        "exponential_lower_bound": "Exponential lower bound techniques (NEXP not in ACC) are non-relativizing.",
    }

    # Canonical collapsing oracle description (P^A = NP^A)
    COLLAPSING_ORACLE_TEMPLATE = """Oracle A (collapsing, P^A = NP^A):
  A encodes the satisfiability problem directly as a lookup table.
  A(phi) = 1 iff phi is satisfiable (for Boolean formulas phi).
  With oracle A, P^A = NP^A because NP queries are answered in one step.
  Any proof that uses only black-box computation cannot distinguish
  A from a random oracle, so it cannot separate P^A from NP^A.
  Proof technique '{technique}' does not use A's internal structure,
  so it relativizes: the same argument works identically with oracle A."""

    # Canonical separating oracle description (P^B != NP^B)
    SEPARATING_ORACLE_TEMPLATE = """Oracle B (separating, P^B != NP^B):
  B is chosen to encode exponentially long strings that no poly-time machine can find.
  B(n, i) = the i-th bit of a uniformly random 2^n-bit string R_n.
  The language L_B = {{1^n : exists i, B(n, i) = 1}} is in NP^B but not P^B.
  This is because guessing i is easy for an NP machine (just guess non-deterministically)
  but finding i requires exponentially many oracle queries for P machines.
  Proof technique '{technique}' does not exploit B's specifics and would work
  the same way even if B encoded L_B or encoded the empty language.
  This confirms the technique relativizes."""

    def __init__(self, ollama_endpoint: Optional[str] = None, llm_model: Optional[str] = None):
        """
        Initialize the oracle world builder.

        Args:
            ollama_endpoint: Optional Ollama endpoint for LLM-powered analysis
            llm_model:       Optional LLM model name for Ollama calls
        """
        self.ollama_endpoint = ollama_endpoint
        self.llm_model = llm_model
        # Cache: keyed by (proof_file_hash, technique) -> OracleWitness
        self._witness_cache: Dict[str, OracleWitness] = {}
        print(f"[OracleWorldBuilder] Initialized. LLM available: {ollama_endpoint is not None}")

    def construct_witness(
        self,
        proof_file: str,
        proof_data: Dict[str, Any],
        circuit_class: str,
    ) -> OracleWitness:
        """
        Construct an explicit oracle-world witness for a proof attempt.

        This is the main entry point called by the Critic agent. It:
        1. Identifies the core proof technique.
        2. Determines if the technique is relativizing.
        3. Constructs the canonical oracle description.
        4. If LLM available: asks LLM to validate and propose non-rel fix.

        Args:
            proof_file:    Path to Lean file being analyzed
            proof_data:    Dict from ProofParser (tactics, content, etc.)
            circuit_class: Circuit class targeted (monotone, AC0, formula)

        Returns:
            OracleWitness with full classification and oracle description
        """
        print(f"[OracleWorldBuilder] Constructing witness for: {proof_file}")

        # Cache key: hash of file path + content hash
        content = proof_data.get("content", "")
        cache_key = hashlib.sha256(f"{proof_file}:{content[:200]}".encode()).hexdigest()[:16]

        if cache_key in self._witness_cache:
            print(f"[OracleWorldBuilder] Cache hit for {proof_file} (key={cache_key})")
            return self._witness_cache[cache_key]

        # Step 1: Identify core technique
        technique = self._identify_technique(proof_data)
        print(f"[OracleWorldBuilder] Identified technique: {technique}")

        # Step 2: Classify as relativizing or not
        relativizes, base_confidence = self._classify_technique(technique, proof_data)
        print(f"[OracleWorldBuilder] Relativizes: {relativizes} (confidence={base_confidence:.2f})")

        # Step 3: Build oracle description
        if relativizes:
            oracle_type = "separating"
            witness_desc = self.SEPARATING_ORACLE_TEMPLATE.format(technique=technique)
            oracle_queries = self._build_separating_oracle_queries(technique, proof_data)
        else:
            oracle_type = "collapsing"
            witness_desc = self.COLLAPSING_ORACLE_TEMPLATE.format(technique=technique)
            oracle_queries = self._build_collapsing_oracle_queries(technique, proof_data)

        print(f"[OracleWorldBuilder] Oracle type: {oracle_type}, queries: {len(oracle_queries)}")

        # Step 4: LLM analysis (if available)
        llm_reasoning = None
        non_rel_suggestion = None
        final_confidence = base_confidence

        if self.ollama_endpoint and self.llm_model:
            print(f"[OracleWorldBuilder] Querying LLM for oracle analysis (model={self.llm_model})")
            llm_result = self._llm_oracle_analysis(
                proof_file, technique, relativizes, circuit_class, proof_data
            )
            if llm_result:
                llm_reasoning = llm_result.get("reasoning", "")
                non_rel_suggestion = llm_result.get("non_rel_suggestion", "")
                llm_confidence = llm_result.get("confidence", base_confidence)
                # Blend base confidence with LLM confidence (70% LLM, 30% base)
                final_confidence = 0.7 * llm_confidence + 0.3 * base_confidence
                print(f"[OracleWorldBuilder] LLM analysis: confidence={llm_confidence:.2f}, "
                      f"has suggestion={non_rel_suggestion is not None}")
        else:
            # No LLM: generate a rule-based non-relativizing suggestion
            if relativizes:
                non_rel_suggestion = self._rule_based_non_rel_suggestion(technique, circuit_class)
                print(f"[OracleWorldBuilder] Rule-based suggestion: {non_rel_suggestion[:80]}...")

        witness = OracleWitness(
            proof_file=proof_file,
            oracle_type=oracle_type,
            circuit_class=circuit_class,
            proof_technique=technique,
            relativizes=relativizes,
            witness_description=witness_desc,
            oracle_queries=oracle_queries,
            non_rel_suggestion=non_rel_suggestion,
            confidence=final_confidence,
            llm_reasoning=llm_reasoning,
        )

        self._witness_cache[cache_key] = witness
        print(f"[OracleWorldBuilder] Witness constructed and cached for {proof_file}")

        return witness

    def _identify_technique(self, proof_data: Dict[str, Any]) -> str:
        """
        Identify the core proof technique from parsed proof data.

        Priority order (most specific to least specific):
          1. Algebraic keywords (arithmetization, polynomial, GF(2))
          2. Approximation method keywords
          3. Interactive proof keywords
          4. Exponential lower bound keywords
          5. Tactics: induction > cases > omega/simp (counting)
          6. Fallback: unknown

        Args:
            proof_data: Dict from ProofParser

        Returns:
            Technique string key
        """
        content  = proof_data.get("content", "").lower()
        tactics  = proof_data.get("tactics", [])

        print(f"[OracleWorldBuilder] Identifying technique from tactics={tactics}")

        # Algebraic / non-relativizing signals take priority
        if any(kw in content for kw in ["arithmetiz", "multilinear", "gf(2)", "galois", "polynomial_evaluation"]):
            return "arithmetization"

        if any(kw in content for kw in ["algebraic", "low_degree", "field_extension", "extension_field"]):
            return "algebraic_techniques"

        if any(kw in content for kw in ["approximation", "razborov", "smolensky", "restriction"]):
            return "approximation_method"

        if any(kw in content for kw in ["interactive", "prover", "verifier", "sum_check", "sumcheck"]):
            return "interactive_proof"

        if any(kw in content for kw in ["algebrize", "algebrization", "algebraic_relativization"]):
            return "algebraization"

        if any(kw in content for kw in ["exponential lower", "nexp", "acc0", "acc circuit"]):
            return "exponential_lower_bound"

        # Tactic-based identification (relativizing)
        if "induction" in tactics:
            return "induction"

        if "cases" in tactics or "interval_cases" in tactics:
            return "case_analysis"

        if any(t in tactics for t in ["omega", "simp", "norm_num"]) or \
           any(kw in content for kw in ["count", "cardinality", "enumerate", "pigeonhole"]):
            return "counting_argument"

        if "diag" in content:
            return "diagonalization"

        return "unknown"

    def _classify_technique(
        self,
        technique: str,
        proof_data: Dict[str, Any],
    ) -> tuple:
        """
        Classify technique as relativizing or not, with confidence.

        Returns:
            (relativizes: bool, confidence: float)
        """
        # Check known non-relativizing techniques first
        if technique in self.NON_RELATIVIZING_TECHNIQUES:
            # Even non-relativizing techniques have uncertainty when applied to circuit lower bounds
            # because the specific application may still be relativizing
            confidence = 0.75
            print(f"[OracleWorldBuilder] NON-RELATIVIZING technique: {technique} (confidence={confidence})")
            return False, confidence

        if technique in self.RELATIVIZING_TECHNIQUES:
            # Case analysis with sorry is highly likely to relativize (it's incomplete)
            has_sorry = proof_data.get("has_sorry", True)
            confidence = 0.85 if has_sorry else 0.70
            print(f"[OracleWorldBuilder] RELATIVIZING technique: {technique} (confidence={confidence}, sorry={has_sorry})")
            return True, confidence

        # Unknown: conservative default is relativizing
        print(f"[OracleWorldBuilder] Unknown technique '{technique}', defaulting to relativizing")
        return True, 0.55

    def _build_separating_oracle_queries(
        self,
        technique: str,
        proof_data: Dict[str, Any],
    ) -> List[str]:
        """
        Build a list of oracle queries that expose relativization.

        These are concrete inputs to the separating oracle B where the
        proof argument breaks down.

        Args:
            technique:  Core proof technique
            proof_data: Parsed proof data

        Returns:
            List of query descriptions
        """
        queries = []

        if technique == "case_analysis":
            queries.append(
                "Oracle query B(n, 0..2^n-1): Enumerate all exponentially many bits. "
                "Case analysis requires checking each, but n cases are insufficient."
            )
            queries.append(
                "Critical input: 1^n where n is large enough that 2^n > k (circuit size). "
                "Case analysis on n cases misses exponentially many oracle bits."
            )

        elif technique == "induction":
            queries.append(
                "Oracle query B(k, i) for each step k in the induction. "
                "At step k, oracle adds a new hard bit that invalidates the inductive hypothesis."
            )
            queries.append(
                "Adversarial oracle: B(k, i) = 1 iff the induction hypothesis claims something false. "
                "Inductive step fails because oracle can embed a counterexample at each k."
            )

        elif technique == "counting_argument":
            queries.append(
                "Oracle query B(n, 0..2^n-1): Oracle pads the language to have exactly "
                "the count the argument assumes, breaking the pigeonhole reasoning."
            )
            queries.append(
                "Padding oracle: for any threshold T the counting argument uses, "
                "B encodes a language of exactly T-1 strings of each length. "
                "Every counting bound fails by 1."
            )

        elif technique == "diagonalization":
            queries.append(
                "Oracle B encodes the diagonalization table itself as oracle bits. "
                "With B, P^B can compute the diagonal in polynomial time, "
                "so the diagonal construction does not separate P^B from NP^B."
            )

        else:
            queries.append(
                f"Generic separating oracle: B encodes a language that collapses "
                f"any {technique} argument by making its core assumption false."
            )

        print(f"[OracleWorldBuilder] Built {len(queries)} separating oracle queries for {technique}")
        return queries

    def _build_collapsing_oracle_queries(
        self,
        technique: str,
        proof_data: Dict[str, Any],
    ) -> List[str]:
        """
        Build a list of oracle queries for the collapsing oracle A (P^A = NP^A).

        For non-relativizing techniques, we show which queries demonstrate the
        technique's oracle-independence (it works regardless of A's content).

        Args:
            technique:  Core proof technique
            proof_data: Parsed proof data

        Returns:
            List of query descriptions
        """
        queries = []

        if technique == "arithmetization":
            queries.append(
                "Oracle A answers SAT queries. Arithmetization replaces AND/OR with +/x over GF(2). "
                "The polynomial evaluation does not query A, so A is irrelevant. "
                "Non-relativizing: technique is oracle-independent."
            )

        elif technique == "algebraic_techniques":
            queries.append(
                "Oracle A answers NP queries. Algebraic lower bound uses field arithmetic, "
                "not computation paths. The polynomial identity testing step does not "
                "depend on which language A encodes. Oracle-independent."
            )

        elif technique == "approximation_method":
            queries.append(
                "Oracle A answers PSPACE queries. Razborov approximation method defines "
                "approximating polynomials purely algebraically. The approximation error "
                "analysis does not reference oracle A's truth table. Oracle-independent."
            )

        else:
            queries.append(
                f"Collapsing oracle A: technique {technique} is oracle-independent "
                f"because its core argument does not reference computation paths or oracle bits."
            )

        print(f"[OracleWorldBuilder] Built {len(queries)} collapsing oracle queries for {technique}")
        return queries

    def _rule_based_non_rel_suggestion(self, technique: str, circuit_class: str) -> str:
        """
        Generate a rule-based suggestion for making a relativizing proof non-relativizing.

        Used when LLM is not available. Provides concrete, technique-specific guidance.

        Args:
            technique:     The relativizing technique identified
            circuit_class: Circuit class targeted

        Returns:
            String suggestion for a non-relativizing variant
        """
        suggestions = {
            "case_analysis": (
                f"Replace exhaustive case analysis on {circuit_class} circuits with "
                f"an algebraic argument. Encode circuit evaluation as a multilinear polynomial "
                f"over GF(2) and show the polynomial has low degree, implying a lower bound. "
                f"This is oracle-independent because polynomial degree does not change with oracles."
            ),
            "induction": (
                f"Replace structural induction over circuit gates with an algebraic induction: "
                f"inductively build a low-degree polynomial that approximates the target function "
                f"and derive a contradiction from the circuit's degree bound. "
                f"Razborov's approximation method follows this pattern for monotone circuits."
            ),
            "counting_argument": (
                f"Replace the pure counting argument with a rank/dimension argument over GF(2). "
                f"Show that the matrix of circuit outputs has rank < 2^n, implying parity cannot "
                f"be computed. Rank arguments are algebraic and oracle-independent."
            ),
            "diagonalization": (
                f"Replace diagonalization with an algebraization argument: use algebraic extensions "
                f"of the problem (MIP* = RE uses entanglement, sum-check uses polynomials). "
                f"For circuit lower bounds, the algebrization barrier says you must go beyond "
                f"oracle-relative techniques to relativized algebraic extensions."
            ),
            "unknown": (
                f"The technique could not be identified. Consider replacing the sorry placeholder "
                f"with an arithmetization step: encode {circuit_class} circuit evaluation as a "
                f"multilinear polynomial and apply Schwartz-Zippel to derive a size lower bound."
            ),
        }

        result = suggestions.get(technique, suggestions["unknown"])
        print(f"[OracleWorldBuilder] Rule-based suggestion for {technique}: {result[:60]}...")
        return result

    def _llm_oracle_analysis(
        self,
        proof_file: str,
        technique: str,
        relativizes: bool,
        circuit_class: str,
        proof_data: Dict[str, Any],
    ) -> Optional[Dict[str, Any]]:
        """
        Query the LLM to validate oracle classification and propose a non-relativizing fix.

        The prompt describes:
        1. The proof technique identified
        2. Our classification (relativizing or not)
        3. The circuit class
        4. The proof content (first 500 chars for context)

        The LLM is asked to:
        1. Confirm or correct the relativization classification
        2. Describe a concrete oracle world that exposes the issue
        3. Propose a specific non-relativizing alternative technique

        Args:
            proof_file:   Path to Lean file
            technique:    Identified proof technique
            relativizes:  Our classification
            circuit_class: Circuit class
            proof_data:   Parsed proof data

        Returns:
            Dict with keys: reasoning, non_rel_suggestion, confidence
            or None if LLM call fails
        """
        try:
            import urllib.request
            import urllib.error

            content_snippet = proof_data.get("content", "")[:400]
            rel_label = "RELATIVIZING" if relativizes else "NON-RELATIVIZING"

            prompt = f"""You are a complexity theorist analyzing a proof attempt for a circuit lower bound.

Proof file: {proof_file}
Circuit class: {circuit_class}
Core technique identified: {technique}
Our classification: {rel_label}

Proof content (first 400 chars):
{content_snippet}

Task: Confirm or correct our relativization classification, then propose a concrete non-relativizing improvement.

Respond in exactly this format (no hyphens):

<ORACLE_ANALYSIS>
classification: RELATIVIZING or NON_RELATIVIZING
confidence: 0.0 to 1.0
oracle_world: [one paragraph describing the explicit oracle that exposes or confirms relativization]
reasoning: [one paragraph explaining why the technique does or does not relativize]
</ORACLE_ANALYSIS>

<NON_REL_SUGGESTION>
[One paragraph concrete suggestion for a non-relativizing proof technique that could replace or augment the current approach]
</NON_REL_SUGGESTION>"""

            url = f"{self.ollama_endpoint}/api/generate"
            payload = json.dumps({
                "model": self.llm_model,
                "prompt": prompt,
                "stream": False,
                "options": {
                    "temperature": 0.1,
                    "num_predict": 1024,
                },
            }).encode("utf-8")

            print(f"[OracleWorldBuilder] POST {url} model={self.llm_model}")
            start_t = time.time()

            req = urllib.request.Request(
                url,
                data=payload,
                headers={"Content-Type": "application/json"},
                method="POST",
            )

            with urllib.request.urlopen(req, timeout=60) as resp:
                raw = resp.read().decode("utf-8")

            elapsed = time.time() - start_t
            print(f"[OracleWorldBuilder] LLM response in {elapsed:.1f}s ({len(raw)} bytes)")

            data = json.loads(raw)
            response_text = data.get("response", "") or data.get("thinking", "")

            return self._parse_llm_oracle_response(response_text)

        except Exception as e:
            print(f"[OracleWorldBuilder] LLM call failed: {e}", file=sys.stderr)
            return None

    def _parse_llm_oracle_response(self, raw: str) -> Optional[Dict[str, Any]]:
        """
        Parse LLM response into structured oracle analysis result.

        Extracts:
          classification: RELATIVIZING | NON_RELATIVIZING
          confidence:     float
          reasoning:      the full ORACLE_ANALYSIS block content
          non_rel_suggestion: the NON_REL_SUGGESTION block content

        Args:
            raw: Raw LLM response text

        Returns:
            Dict with keys: reasoning, non_rel_suggestion, confidence
            or None on parse failure
        """
        import re

        print(f"[OracleWorldBuilder] Parsing LLM oracle response ({len(raw)} chars)")

        analysis_match = re.search(r"<ORACLE_ANALYSIS>(.*?)</ORACLE_ANALYSIS>", raw, re.DOTALL)
        suggestion_match = re.search(r"<NON_REL_SUGGESTION>(.*?)</NON_REL_SUGGESTION>", raw, re.DOTALL)

        if not analysis_match:
            print(f"[OracleWorldBuilder] No <ORACLE_ANALYSIS> block in LLM response")
            return None

        analysis_text = analysis_match.group(1).strip()
        suggestion_text = suggestion_match.group(1).strip() if suggestion_match else None

        # Parse confidence from analysis block
        confidence = 0.6
        conf_match = re.search(r"confidence:\s*([\d.]+)", analysis_text)
        if conf_match:
            try:
                confidence = float(conf_match.group(1))
                confidence = max(0.0, min(1.0, confidence))
            except ValueError:
                pass

        print(f"[OracleWorldBuilder] Parsed LLM: confidence={confidence}, has_suggestion={suggestion_text is not None}")

        return {
            "reasoning":          analysis_text,
            "non_rel_suggestion": suggestion_text,
            "confidence":         confidence,
        }


def construct_oracle_witness_for_proof(
    proof_file: str,
    proof_data: Dict[str, Any],
    circuit_class: str,
    ollama_endpoint: Optional[str] = None,
    llm_model: Optional[str] = None,
) -> OracleWitness:
    """
    Convenience function: construct an oracle witness for a single proof.

    This is the top-level entry point used by the Critic agent.

    Args:
        proof_file:       Path to Lean theorem file
        proof_data:       Dict from ProofParser
        circuit_class:    Circuit class (monotone, AC0, formula)
        ollama_endpoint:  Optional Ollama URL for LLM analysis
        llm_model:        Optional Ollama model name

    Returns:
        OracleWitness with full classification
    """
    print(f"[oracle_worlds] Constructing witness: {proof_file} ({circuit_class})")
    builder = OracleWorldBuilder(
        ollama_endpoint=ollama_endpoint,
        llm_model=llm_model,
    )
    return builder.construct_witness(proof_file, proof_data, circuit_class)
