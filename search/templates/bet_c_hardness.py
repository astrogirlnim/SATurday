"""
Bet C: Hardness-vs-Randomness Templates.

Generates conjectures that probe the Nisan-Wigderson hardness-randomness
connection. Each conjecture encodes a micro-implication of the form:

  "If f is hard for small circuits, then a PRG based on f fools small circuits."

The SAT encoding asks:
  "Does a size-k circuit C exist such that:
     C distinguishes the output of the PRG from truly random strings?"
  UNSAT => PRG is secure against circuits of that size (hardness implies randomness).
  SAT   => circuit witness is a distinguisher (randomness side fails at this size).

Additionally, we encode correlation tests:
  For a circuit-function pair (C, f), compute the empirical correlation of C
  with f on all 2^n inputs. Low correlation => C is a poor approximation of f
  => f is hard for circuits of size k.

Templates:
  HardnessCorrelationTemplate  : measures correlation of size-k circuits with f
  PRGSecurityTemplate          : checks if PRG_f fools size-k circuits
  NisanWigdersonImplicationTemplate : formalizes H => R micro-implication in Lean
"""

from typing import Any, Dict
from .base import ConjectureTemplate


class HardnessCorrelationTemplate(ConjectureTemplate):
    """
    Template for hardness correlation tests.

    Asks: Does a monotone circuit of size <= k compute a function that
    correlates with parity on >= (1/2 + epsilon) fraction of 2^n inputs?

    UNSAT => no small circuit achieves non-trivial correlation.
          => f is hard for size-k circuits (circuit complexity lower bound).
    SAT   => witness circuit C achieves the target correlation.

    This is a tight encoding of the Razborov/Smolensky line: parity is
    hard for AC0 because no small-depth circuit approximates parity well.
    """

    def __init__(self):
        super().__init__("bet_c_hardness_correlation", "C")

    def generate_lean_stub(self, **params) -> str:
        n        = params.get("n", 4)
        seed     = params.get("seed", 0)
        task_id  = params.get("task_id", "unknown")
        k        = params.get("max_gates", n * n)
        epsilon  = params.get("epsilon", 0.1)
        func     = params.get("function_name", "parity")
        circuit  = params.get("circuit_type", "monotone")

        return f"""import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetC

/-!
# Hardness-vs-Randomness: Correlation Test

Conjecture: No {circuit} circuit of size <= {k} achieves correlation
> (1/2 + {epsilon}) with {func} on {n} inputs.

## Encoding
For each truth table row i in 0..2^{n}-1:
  Let x_i = the {n}-bit input corresponding to i.
  Let f(x_i) = the target function ({func}) output.
  Circuit variable c_i in {{0,1}} represents C(x_i).
  Correlation = |{{i : c_i = f(x_i)}}| / 2^{n}.

Clause encoding:
  The synthesis variables pick gates for C.
  Additional clauses enforce: sum(c_i == f(x_i)) <= (1/2 + {epsilon}) * 2^{n}.
  If UNSAT: no circuit of size <= {k} achieves that correlation. QED lower bound.

## Significance
Low correlation for all small circuits means f is hard in the
Razborov-Smolensky sense. This is the quantitative hardness side of H<=>R.

## Task
task_id : {task_id}
seed    : {seed}
-/

-- Represent circuit correlation as a Nat count of agreeing inputs
def correlation_count (n : Nat) (circuit_outputs : Fin (2^n) -> Bool)
    (target : Fin (2^n) -> Bool) : Nat :=
  -- Count inputs where circuit agrees with target function
  (Finset.univ (α := Fin (2^n))).filter
    (fun i => circuit_outputs i == target i) |>.card

-- The hardness conjecture: parity is uncorrelated with small circuits
theorem hardness_correlation_n{n}_k{k}_s{seed} :
    -- For all circuits of size <= {k}, correlation with {func} is at most 1/2 + {epsilon}
    True := by
  -- TODO: Fill in using LRAT witness from SAT solver
  -- If UNSAT, the encoding below proves no such high-correlation circuit exists
  sorry

end SATurday.Conjectures.BetC
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n        = params.get("n", 4)
        seed     = params.get("seed", 0)
        task_id  = params.get("task_id", "unknown")
        k        = params.get("max_gates", n * n)
        epsilon  = params.get("epsilon", 0.1)
        func     = params.get("function_name", "parity")
        circuit  = params.get("circuit_type", "monotone")

        print(f"[HardnessCorrelationTemplate] Generating CNF spec: n={n}, k={k}, circuit={circuit}, func={func}")

        return {
            "conjecture_id": f"bet_c_correlation_{circuit}_{func}_n{n}_s{seed}",
            "task_id": task_id,
            "description": (
                f"Hardness correlation test: does a {circuit} circuit of size {k} "
                f"correlate > 0.5+{epsilon} with {func} on {n} inputs?"
            ),
            "circuit": {
                "type": circuit,
                "num_inputs": n,
                "max_gates": k,
            },
            "target_function": {
                "name": func,
                "n": n,
            },
            "correlation": {
                "epsilon": epsilon,
                "threshold": 0.5 + epsilon,
                "interpretation": "UNSAT means no circuit achieves threshold correlation",
            },
            "encoding": {
                "method": "circuit_synthesis",
                "mode": "correlation_test",
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": 120,
            },
        }

    def instantiate(self, task: Dict[str, Any]) -> Any:
        """
        Create a Conjecture from a planner task dict.

        Maps task fields to template parameters and generates both
        the Lean stub and CNF spec.
        """
        print(f"[HardnessCorrelationTemplate] Instantiating for task: {task.get('task_id')}")

        from .base import Conjecture

        n           = task.get("problem_size", 4)
        seed        = task.get("seed", 0)
        task_id     = task.get("task_id", "unknown")
        circuit     = task.get("circuit_type", "monotone")
        func        = task.get("function_name", "parity")
        max_gates   = n * n
        epsilon     = 0.1  # Fixed epsilon for MVP; could be config-driven

        params = {
            "n": n,
            "seed": seed,
            "task_id": task_id,
            "max_gates": max_gates,
            "epsilon": epsilon,
            "function_name": func,
            "circuit_type": circuit,
        }

        lean_stub = self.generate_lean_stub(**params)
        cnf_spec  = self.generate_cnf_spec(**params)

        conjecture_id = f"bet_c_corr_{circuit}_{func}_n{n}_s{seed}"

        return Conjecture(
            conjecture_id=conjecture_id,
            task_id=task_id,
            bet="C",
            lean_stub=lean_stub,
            cnf_spec=cnf_spec,
            metadata={
                "template_id": self.template_id,
                "problem_size": n,
                "seed": seed,
                "circuit_type": circuit,
                "function_name": func,
                "epsilon": epsilon,
                "max_gates": max_gates,
            },
        )


class PRGSecurityTemplate(ConjectureTemplate):
    """
    Template for PRG security conjecture encoding.

    Asks: Does a size-k circuit distinguish the output of PRG_f from random?

    The PRG_f (Nisan-Wigderson generator based on f) stretches l-bit seeds to
    m-bit outputs. A distinguishing circuit C of size k satisfies:
      |Pr[C(PRG_f(s)) = 1] - Pr[C(r) = 1]| > delta

    UNSAT => no size-k circuit distinguishes PRG_f from random.
          => PRG_f is (k, delta)-secure. This is the randomness side of H<=>R.
    SAT   => witness circuit C is an explicit distinguisher.
    """

    def __init__(self):
        super().__init__("bet_c_prg_security", "C")

    def generate_lean_stub(self, **params) -> str:
        n       = params.get("n", 4)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        k       = params.get("max_gates", n * n)
        delta   = params.get("delta", 0.1)
        func    = params.get("function_name", "parity")

        return f"""import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetC

/-!
# Hardness-vs-Randomness: PRG Security

Conjecture: The Nisan-Wigderson PRG based on {func} is secure against
all circuits of size <= {k} with distinguishing advantage <= {delta}.

## Generator Construction
For f : {{0,1}}^{n} -> {{0,1}} hard for size-k circuits:
  PRG_f(s) = (f(s[I_1]), ..., f(s[I_m]))
  where I_1, ..., I_m are carefully chosen index sets of size {n}.

## SAT Encoding
Variables: gate types and wiring of a candidate distinguisher circuit D of size {k}.
Clauses enforce:
  |{{seeds s : D(PRG_f(s)) = 1}} / 2^l| - |{{r random : D(r) = 1}}| > {delta}
UNSAT => no such D exists => PRG is ({k}, {delta})-secure.

## Significance
If f is hard for size-k circuits, then PRG_f fools size-k circuits.
This formalizes one direction of the Nisan-Wigderson H<=>R theorem
for small parameters.

## Task
task_id : {task_id}
seed    : {seed}
-/

-- PRG security definition
def prg_secure (k : Nat) (delta : Float) : Prop :=
  -- No circuit of size k distinguishes PRG output from random
  True  -- placeholder: filled by LRAT witness

theorem prg_security_{func}_n{n}_k{k}_s{seed} :
    prg_secure {k} {delta} := by
  sorry

end SATurday.Conjectures.BetC
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n       = params.get("n", 4)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        k       = params.get("max_gates", n * n)
        delta   = params.get("delta", 0.1)
        func    = params.get("function_name", "parity")
        circuit = params.get("circuit_type", "monotone")

        print(f"[PRGSecurityTemplate] Generating CNF spec: n={n}, k={k}, func={func}, delta={delta}")

        return {
            "conjecture_id": f"bet_c_prg_{func}_n{n}_s{seed}",
            "task_id": task_id,
            "description": (
                f"PRG security test: can a circuit of size {k} distinguish "
                f"PRG_{func}(seed) from random with advantage > {delta}?"
            ),
            "circuit": {
                "type": circuit,
                "num_inputs": n,
                "max_gates": k,
            },
            "target_function": {
                "name": func,
                "n": n,
            },
            "prg": {
                "base_function": func,
                "seed_length": n,
                "output_length": n * 2,
                "delta": delta,
                "interpretation": "UNSAT means PRG is secure against circuits of this size",
            },
            "encoding": {
                "method": "circuit_synthesis",
                "mode": "prg_distinguisher",
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": 120,
            },
        }

    def instantiate(self, task: Dict[str, Any]) -> Any:
        """Create a Conjecture from a planner task dict."""
        print(f"[PRGSecurityTemplate] Instantiating for task: {task.get('task_id')}")

        from .base import Conjecture

        n         = task.get("problem_size", 4)
        seed      = task.get("seed", 0)
        task_id   = task.get("task_id", "unknown")
        circuit   = task.get("circuit_type", "monotone")
        func      = task.get("function_name", "parity")
        max_gates = n * n
        delta     = 0.1

        params = {
            "n": n,
            "seed": seed,
            "task_id": task_id,
            "max_gates": max_gates,
            "delta": delta,
            "function_name": func,
            "circuit_type": circuit,
        }

        lean_stub = self.generate_lean_stub(**params)
        cnf_spec  = self.generate_cnf_spec(**params)

        conjecture_id = f"bet_c_prg_{func}_n{n}_s{seed}"

        return Conjecture(
            conjecture_id=conjecture_id,
            task_id=task_id,
            bet="C",
            lean_stub=lean_stub,
            cnf_spec=cnf_spec,
            metadata={
                "template_id": self.template_id,
                "problem_size": n,
                "seed": seed,
                "circuit_type": circuit,
                "function_name": func,
                "delta": delta,
                "max_gates": max_gates,
            },
        )


class NisanWigdersonImplicationTemplate(ConjectureTemplate):
    """
    Template for Nisan-Wigderson H<=>R micro-implication.

    Formalizes the statement: "If f requires circuits of size k, then PRG_f
    fools circuits of size k/n." This is the core quantitative H<=>R implication
    for bounded circuit sizes, formalized as a Lean theorem stub.

    The SAT encoding checks the contrapositive: if a distinguisher D of size k/n
    exists for PRG_f, then a circuit of size k computing f exists (via the
    reconstruction argument). This entangles both sides of the implication
    into a single SAT check.
    """

    def __init__(self):
        super().__init__("bet_c_nw_implication", "C")

    def generate_lean_stub(self, **params) -> str:
        n       = params.get("n", 4)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        k       = params.get("max_gates", n * n)
        func    = params.get("function_name", "parity")

        return f"""import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

namespace SATurday.Conjectures.BetC

/-!
# Nisan-Wigderson H<=>R Micro-Implication

Conjecture: For f = {func} on {n} inputs, hardness of f for size-{k} circuits
implies PRG_f is secure against size-{k // n} circuits.

## Formal Statement
For any delta > 0:
  (forall C of size {k}, Pr[C(x) = f(x)] <= 1/2 + delta)
  =>
  (forall D of size {k // n}, |Pr[D(PRG_f(s))=1] - Pr[D(r)=1]| <= n * delta)

This is the quantitative Nisan-Wigderson theorem restricted to
circuit sizes ({k}, {k // n}) and {n}-bit inputs.

## Why This Matters for P vs NP
If we can prove hardness lower bounds for f at all polynomial sizes
(not just specific k), and stack this H<=>R implication, we get
unconditional PRG constructions from circuit lower bounds.
This is one viable path toward derandomization without assuming crypto.

## Task
task_id : {task_id}
seed    : {seed}
-/

-- Hardness predicate: f requires large circuits
def is_hard (n k : Nat) (f : Fin (2^n) -> Bool) : Prop :=
  True  -- placeholder: formalized via LRAT lower bound proofs

-- PRG security predicate  
def prg_fooling (n k_prg : Nat) (f : Fin (2^n) -> Bool) : Prop :=
  True  -- placeholder: formalized via PRG distinguishing SAT check

-- The Nisan-Wigderson micro-implication
theorem nw_implication_{func}_n{n}_k{k}_s{seed} :
    is_hard {n} {k} (fun _ => false) -> prg_fooling {n} {k // n} (fun _ => false) := by
  intro _h_hard
  -- TODO: Fill in via reconstruction argument
  -- If PRG is not fooling, we reconstruct a circuit for f
  sorry

end SATurday.Conjectures.BetC
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n       = params.get("n", 4)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        k       = params.get("max_gates", n * n)
        func    = params.get("function_name", "parity")
        circuit = params.get("circuit_type", "monotone")

        print(f"[NWImplicationTemplate] Generating CNF spec: n={n}, k={k}, func={func}")

        return {
            "conjecture_id": f"bet_c_nw_{func}_n{n}_s{seed}",
            "task_id": task_id,
            "description": (
                f"NW implication: hardness of {func} at size {k} implies PRG security at size {k // max(n, 1)}"
            ),
            "circuit": {
                "type": circuit,
                "num_inputs": n,
                "max_gates": k,
            },
            "target_function": {
                "name": func,
                "n": n,
            },
            "implication": {
                "hardness_size": k,
                "prg_security_size": k // max(n, 1),
                "type": "nisan_wigderson",
                "interpretation": "UNSAT means contrapositive holds: no distinguisher => hardness implied",
            },
            "encoding": {
                "method": "circuit_synthesis",
                "mode": "implication_check",
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": 120,
            },
        }

    def instantiate(self, task: Dict[str, Any]) -> Any:
        """Create a Conjecture from a planner task dict."""
        print(f"[NWImplicationTemplate] Instantiating for task: {task.get('task_id')}")

        from .base import Conjecture

        n         = task.get("problem_size", 4)
        seed      = task.get("seed", 0)
        task_id   = task.get("task_id", "unknown")
        circuit   = task.get("circuit_type", "monotone")
        func      = task.get("function_name", "parity")
        max_gates = n * n

        params = {
            "n": n,
            "seed": seed,
            "task_id": task_id,
            "max_gates": max_gates,
            "function_name": func,
            "circuit_type": circuit,
        }

        lean_stub = self.generate_lean_stub(**params)
        cnf_spec  = self.generate_cnf_spec(**params)

        conjecture_id = f"bet_c_nw_{func}_n{n}_s{seed}"

        return Conjecture(
            conjecture_id=conjecture_id,
            task_id=task_id,
            bet="C",
            lean_stub=lean_stub,
            cnf_spec=cnf_spec,
            metadata={
                "template_id": self.template_id,
                "problem_size": n,
                "seed": seed,
                "circuit_type": circuit,
                "function_name": func,
                "max_gates": max_gates,
            },
        )
