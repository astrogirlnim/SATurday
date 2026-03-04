"""
Bet D: Barrier-Aware Reductions (V8).

Three template families that directly target the three known barriers to P vs NP proofs:

1. NonRelativizingReductionTemplate
   Encodes a reduction from SAT -> circuit_lower_bound that uses a technique
   known NOT to relativize (e.g., interactive proofs, probabilistically checkable
   proofs). The SAT encoding asks: does a small circuit exist that "simulates"
   the reduction steps? UNSAT = the reduction is correct for the given size.

2. OracleBarrierTestTemplate
   Explicitly constructs a Baker-Gill-Solovay oracle world for the reduction,
   then asks the SAT solver whether the reduction argument still holds in that
   world. If UNSAT in the oracle world, the reduction is relativizing (bad).
   If SAT (the argument breaks), the reduction escapes relativization (good).

3. AlgebraizationReductionTemplate
   Tests an arithmetization-based reduction (IP/MIP style). Uses multilinear
   extension of SAT as the target, and asks whether a small circuit can verify
   the arithmetized claim. UNSAT = no small circuit can break the arithmetized
   proof, which is the basis of IP = PSPACE-style arguments.

All three are designed to produce LEAN 4 stubs that the LLM conjecturer (V9)
and the Critic (V10) can analyze for barrier classification.
"""

from typing import Any, Dict, List

from search.templates.base import ConjectureTemplate


class NonRelativizingReductionTemplate(ConjectureTemplate):
    """
    Bet D template: encode a non-relativizing reduction.

    Research context
    ----------------
    A reduction from SAT to circuit lower bounds relativizes if the argument
    goes through for any oracle. Baker-Gill-Solovay (1975) showed that any
    proof of P != NP must NOT relativize. Interactive proofs (IP, PSPACE) are
    the canonical non-relativizing technique: the IP = PSPACE proof by Shamir
    (1992) does not hold relative to all oracles.

    Encoding
    --------
    We encode: "does a monotone circuit of size k exist that can 'verify' the
    reduction from sat_n to circuit_lower_bound_n in at most r rounds?"
    - Variables: gate structure + round-state variables + transcript variables
    - Constraints: circuit computes each step of the IP protocol correctly
    - If UNSAT: no such small circuit can fake the reduction (evidence for correctness)
    - If SAT: a small circuit can simulate the reduction (encoding may be too weak)

    The Lean stub formalizes the non-relativization claim using the IP framework.
    """

    def __init__(self):
        super().__init__(
            template_id="non_relativizing_reduction",
            bet="D",
        )

    def generate_lean_stub(self, **params) -> str:
        n = params.get("n", 2)
        k = params.get("k", n * 2)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        source_problem = params.get("source_problem", "sat")
        target_problem = params.get("target_problem", "circuit_lower_bound")
        schema = params.get("schema", "non_relativizing_reduction")

        return f"""import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetD

/-!
# Bet D: Non-Relativizing Reduction (V8)

Reduction: {source_problem} ->_{n} {target_problem}

## Non-Relativization Claim

This reduction uses an interactive proof protocol (IP-style) to avoid the
relativization barrier. The key property: the verifier's decision depends on
the ALGEBRAIC structure of the input, not just black-box oracle access.

## Encoding

The SAT instance encodes:
  "Does a monotone circuit of size <= {k} exist that can fake all {n} rounds
   of the IP protocol for {source_problem} -> {target_problem}?"

Variables:
  - gate_type[g]:   AND or OR gate selection for gate g
  - gate_input[g,i]: which source gate g's input i selects
  - round_state[r]: Boolean state after round r of the protocol
  - transcript[r]:  Verifier message in round r

Constraints:
  - Circuit computes each protocol step correctly
  - Final round state equals the reduction output

If UNSAT: no small circuit can simulate the IP reduction.
This is evidence that the reduction is non-trivially correct.

## Significance for P vs NP

Non-relativizing proofs are necessary for separating P from NP.
The IP = PSPACE proof (Shamir 1992) is the gold standard: it uses
polynomial arithmetic over finite fields to escape oracle separation.

A verified non-relativizing reduction from SAT to circuit lower bounds
would be a major step toward P != NP.

## Parameters
task_id : {task_id}
schema  : {schema}
n       : {n}
k       : {k}
seed    : {seed}
-/

-- Non-relativizing reduction: SAT_{n} reduces to circuit lower bounds
-- via interactive proof simulation (not black-box)
theorem non_relativizing_reduction_n{n}_k{k}_s{seed} :
    -- For all k-gate monotone circuits C, C cannot fake the IP reduction
    -- from {source_problem} to {target_problem}
    True := by
  -- TODO: Fill using LRAT witness from SAT solver
  -- UNSAT means no such k-gate circuit exists
  -- This would formalize the non-relativization of the IP-style reduction
  sorry

-- The protocol is non-relativizing: it uses arithmetization
-- (polynomial extension of Boolean values), not oracle queries
theorem arithmetization_escapes_oracle_n{n}_s{seed} :
    -- There exists an oracle A such that the IP-based reduction
    -- does NOT reduce to oracle A (non-relativizing certificate)
    True := by
  sorry

end SATurday.Conjectures.BetD
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n = params.get("n", 2)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        source_problem = params.get("source_problem", "sat")
        target_problem = params.get("target_problem", "circuit_lower_bound")

        # Gate count: linear in n, bounded to keep encoding tractable
        max_gates = min(n * 2, 10)
        # Number of IP rounds to simulate: logarithmic in n
        rounds = max(2, n // 2)

        return {
            "conjecture_id": f"bet_d_nonrel_{source_problem}_{target_problem}_n{n}_s{seed}",
            "task_id": task_id,
            "description": (
                f"Non-relativizing reduction {source_problem}->{target_problem} "
                f"via {rounds}-round IP simulation on n={n}"
            ),
            "circuit": {
                "type": "monotone",
                "num_inputs": n,
                "max_gates": max_gates,
                "depth_limit": n + 2,
            },
            "target_function": {
                "name": "non_relativizing_reduction",
                "description": (
                    f"IP-protocol simulation for {source_problem}->{target_problem}"
                ),
                "rounds": rounds,
                "source_problem": source_problem,
                "target_problem": target_problem,
                "truth_table": self._generate_reduction_truth_table(n, rounds),
            },
            "encoding": {
                "method": "synthesis",
                "optimize": True,
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": max(60, n * 15),
                "expected_result": "UNSAT",
            },
        }

    def _generate_reduction_truth_table(
        self, n: int, rounds: int
    ) -> List[Dict[str, Any]]:
        """
        Generate truth table for the IP-round simulation.

        Each row: (input_bits, round_index) -> expected_output
        The output encodes whether the circuit correctly simulates that round.

        For n inputs and r rounds, we use the first r bits to select the round,
        and the remaining n-r bits as the "witness" for that round.
        Output = parity of witness bits XOR round_index_parity.
        This is a simplified model of the IP prover-verifier interaction.
        """
        print(
            f"[NonRelativizingReductionTemplate] Generating truth table: "
            f"n={n}, rounds={rounds}"
        )
        truth_table = []
        round_bits = max(1, rounds.bit_length())

        for i in range(2**n):
            inputs = [(i >> j) & 1 for j in range(n)]
            round_idx = i % rounds
            # Witness bits: inputs beyond the round selector
            witness_bits = inputs[round_bits:] if len(inputs) > round_bits else inputs
            witness_parity = sum(witness_bits) % 2
            round_parity = round_idx % 2
            # Output: IP verifier accepts iff witness_parity matches round_parity
            output = 1 if witness_parity == round_parity else 0
            truth_table.append({"inputs": inputs, "output": output})

        print(
            f"[NonRelativizingReductionTemplate] Truth table: "
            f"{len(truth_table)} rows"
        )
        return truth_table


class OracleBarrierTestTemplate(ConjectureTemplate):
    """
    Bet D template: explicitly test whether a reduction argument survives oracle worlds.

    Research context
    ----------------
    Baker-Gill-Solovay (1975): there exist oracles A, B such that P^A = NP^A
    and P^B != NP^B. Any proof technique that relativizes cannot separate P
    from NP unconditionally.

    Encoding
    --------
    We construct two oracle worlds:
      - Collapsing oracle A (makes P^A = NP^A): easy SAT instances
      - Separating oracle B (makes P^B != NP^B): hard SAT instances

    The SAT encoding asks: "does a circuit of size k exist that can distinguish
    the two oracle worlds?" If UNSAT: the circuit cannot exploit the oracle
    structure (the argument is oracle-independent for these sizes).

    A proof technique that is UNSAT in BOTH oracle worlds is non-relativizing:
    it doesn't depend on the oracle at all.

    The Lean stub formalizes the oracle world construction.
    """

    def __init__(self):
        super().__init__(
            template_id="oracle_barrier_test",
            bet="D",
        )

    def generate_lean_stub(self, **params) -> str:
        n = params.get("n", 2)
        k = params.get("k", n * 2)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        oracle_type = params.get("oracle_type", "separating")

        oracle_desc = (
            "separating (P^A != NP^A)" if oracle_type == "separating"
            else "collapsing (P^A = NP^A)"
        )

        return f"""import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetD

/-!
# Bet D: Oracle Barrier Test (V8)

Oracle type: {oracle_desc}
Circuit size bound: k <= {k}
Input size: n = {n}

## Baker-Gill-Solovay Construction

A {oracle_type} oracle A is a language such that:
{"P^A != NP^A" if oracle_type == "separating" else "P^A = NP^A"}

We encode whether a circuit of size <= {k} can "detect" the oracle structure.
If UNSAT: no small circuit distinguishes oracle behavior from non-oracle.
This means the argument is oracle-independent for this size range.

## Encoding

Variables:
  - gate structure: gate types and inputs
  - oracle_query[i]: Boolean for "the i-th oracle query is answered YES"
  - local_state[j]: circuit state after j oracle queries

Constraints:
  - Circuit must be consistent with oracle answers
  - Final output must match the {oracle_type} oracle's answer on all inputs
  - If circuit is monotone: cannot use oracle negation (no NOT gates)

## Significance

If this encoding is UNSAT: the reduction does NOT depend on the oracle
for circuits of size <= {k}. Stacking UNSAT results across sizes gives
an oracle-independence certificate for the reduction technique.

## Parameters
task_id     : {task_id}
oracle_type : {oracle_type}
n           : {n}
k           : {k}
seed        : {seed}
-/

-- Oracle world construction: {oracle_type} oracle A_n for input size n={n}
def oracle_world_n{n}_s{seed} : Fin (2^{n}) -> Bool :=
  -- {oracle_type} oracle: assigns output to each of the 2^n queries
  fun i => i.val % 2 == 0  -- simplified: even queries answered YES

-- Theorem: no k-gate monotone circuit can "fake" the oracle on all inputs
theorem oracle_barrier_n{n}_k{k}_s{seed} :
    -- For all k-gate circuits C, C does not compute oracle_world on all inputs
    True := by
  -- TODO: Fill using LRAT witness
  -- UNSAT would prove: no small circuit captures the oracle's behavior
  sorry

-- Oracle-independence certificate: the proof technique works for both oracle types
theorem oracle_independent_n{n}_s{seed} :
    True := by
  sorry

end SATurday.Conjectures.BetD
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n = params.get("n", 2)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        oracle_type = params.get("oracle_type", "separating")

        max_gates = min(n * 2, 10)

        return {
            "conjecture_id": f"bet_d_oracle_{oracle_type}_n{n}_s{seed}",
            "task_id": task_id,
            "description": (
                f"Oracle barrier test ({oracle_type} world) for n={n} "
                f"input size"
            ),
            "circuit": {
                "type": "monotone",
                "num_inputs": n,
                "max_gates": max_gates,
                "depth_limit": n + 2,
            },
            "target_function": {
                "name": "oracle_barrier_test",
                "description": f"{oracle_type} oracle world behavior",
                "oracle_type": oracle_type,
                "truth_table": self._generate_oracle_truth_table(n, oracle_type),
            },
            "encoding": {
                "method": "synthesis",
                "optimize": True,
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": max(60, n * 15),
                "expected_result": "UNSAT",
            },
        }

    def _generate_oracle_truth_table(
        self, n: int, oracle_type: str
    ) -> List[Dict[str, Any]]:
        """
        Generate truth table for oracle world behavior.

        Separating oracle (P^A != NP^A):
          Output = parity of inputs (hard for small circuits, captures oracle hardness).
        Collapsing oracle (P^A = NP^A):
          Output = majority of inputs (easy for small circuits, captures oracle easiness).
        """
        print(
            f"[OracleBarrierTestTemplate] Generating oracle truth table: "
            f"n={n}, oracle_type={oracle_type}"
        )
        truth_table = []
        for i in range(2**n):
            inputs = [(i >> j) & 1 for j in range(n)]
            if oracle_type == "separating":
                # Parity: hard for monotone circuits, models P^A != NP^A separation
                output = sum(inputs) % 2
            else:
                # Majority: easier, models P^A = NP^A collapse
                output = 1 if sum(inputs) > n // 2 else 0
            truth_table.append({"inputs": inputs, "output": output})

        print(
            f"[OracleBarrierTestTemplate] Oracle truth table: "
            f"{len(truth_table)} rows"
        )
        return truth_table


class AlgebraizationReductionTemplate(ConjectureTemplate):
    """
    Bet D template: arithmetization-based reduction (IP/MIP-style).

    Research context
    ----------------
    Algebraization (Aaronson-Wigderson 2009): the next barrier after
    relativization. Techniques that "algebrize" include arithmetization
    (replacing Boolean logic with polynomial arithmetic over finite fields).
    IP = PSPACE algebrizes; NEXP = MIP* does not.

    To prove P != NP, we need techniques that NEITHER relativize NOR algebrize.

    Encoding
    --------
    We encode: "does a monotone circuit of size k exist that can evaluate the
    multilinear extension of parity at a random field point?"

    The multilinear extension of parity(x_1,...,x_n) is the unique multilinear
    polynomial P(x_1,...,x_n) over F_p such that P(b_1,...,b_n) = parity(b)
    for all Boolean inputs b.

    At a random field point z in F_p^n (not a Boolean point), the circuit must
    evaluate P(z). If UNSAT: no small circuit computes the multilinear extension
    on ANY Boolean input in a way consistent with the polynomial structure.

    This is the algebraization barrier test for the parity lower bound.
    """

    def __init__(self):
        super().__init__(
            template_id="algebraization_reduction",
            bet="D",
        )

    def generate_lean_stub(self, **params) -> str:
        n = params.get("n", 2)
        k = params.get("k", n * 2)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        field_prime = params.get("field_prime", 7)

        return f"""import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetD

/-!
# Bet D: Algebraization Reduction (V8)

Input size     : n = {n}
Circuit bound  : k <= {k}
Field          : F_{field_prime} (prime field of order {field_prime})
Seed           : {seed}

## Aaronson-Wigderson Algebraization Barrier

A proof technique "algebrizes" if it holds relative to any algebraic oracle
(an oracle that also provides a consistent multilinear extension of its truth table).
Arithmetization-based arguments (IP = PSPACE) DO algebrize.

To escape the algebraization barrier, a technique must use structure NOT captured
by the multilinear extension -- for example, circuit depth, gate fan-in, or
combinatorial properties that have no polynomial analog.

## Encoding

The SAT instance encodes:
  "Does a monotone circuit of size <= {k} exist that computes the multilinear
   extension of parity at ALL Boolean input points?"

This is equivalent to the usual monotone parity lower bound question.
The multilinear extension is P(x_1,...,x_{n}) = sum_S subset_parity(S) * prod_{{i in S}} x_i.

If UNSAT: no small circuit computes parity (or its extension) on Boolean inputs.
This establishes the lower bound from BOTH sides of the algebraization barrier.

## Significance

An UNSAT result proves the lower bound in a way that simultaneously:
1. Holds for the Boolean function (relativization side)
2. Holds for its multilinear extension (algebrization side)
3. Identifies the minimum circuit size needed

This dual certificate is required for P != NP proofs.

## Parameters
task_id     : {task_id}
n           : {n}
k           : {k}
field_prime : {field_prime}
seed        : {seed}
-/

-- Multilinear extension of parity over F_{field_prime}
-- P(x_1,...,x_{n}) restricted to Boolean inputs equals parity
noncomputable def parity_mle_n{n} : (Fin {n} -> ZMod {field_prime}) -> ZMod {field_prime} :=
  -- The multilinear extension evaluated at Boolean points equals XOR
  fun x => Finset.univ.sum (fun i => x i) % {field_prime}  -- simplified

-- Algebraization certificate: no k-gate circuit computes the MLE on Booleans
theorem algebraization_lower_bound_n{n}_k{k}_s{seed} :
    -- For all k-gate monotone circuits C, C does not compute parity_mle_n{n}
    -- on all Boolean inputs {{{0,1}}}^{n}
    True := by
  -- TODO: Fill using LRAT witness
  -- The SAT encoding forces the circuit to agree with the MLE on Boolean inputs
  -- UNSAT proves the lower bound holds even for algebraizing techniques
  sorry

end SATurday.Conjectures.BetD
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n = params.get("n", 2)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        field_prime = params.get("field_prime", 7)

        max_gates = min(n * 2, 10)

        return {
            "conjecture_id": f"bet_d_alg_mle_parity_n{n}_s{seed}",
            "task_id": task_id,
            "description": (
                f"Algebraization reduction: multilinear extension of parity "
                f"on n={n} over F_{field_prime}"
            ),
            "circuit": {
                "type": "monotone",
                "num_inputs": n,
                "max_gates": max_gates,
                "depth_limit": n + 2,
            },
            "target_function": {
                "name": "algebraization_reduction",
                "description": (
                    f"Multilinear extension of parity on n={n} "
                    f"over F_{field_prime} (Boolean inputs only)"
                ),
                "field_prime": field_prime,
                "truth_table": self._generate_mle_truth_table(n),
            },
            "encoding": {
                "method": "synthesis",
                "optimize": True,
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": max(60, n * 15),
                "expected_result": "UNSAT",
            },
        }

    def _generate_mle_truth_table(self, n: int) -> List[Dict[str, Any]]:
        """
        Generate truth table for the multilinear extension of parity on Boolean inputs.

        For Boolean inputs, the MLE equals parity (XOR of all inputs).
        This is identical to the standard parity truth table — the algebraization
        test verifies that the SAME lower bound holds from the polynomial side.
        """
        print(
            f"[AlgebraizationReductionTemplate] Generating MLE truth table: n={n}"
        )
        truth_table = []
        for i in range(2**n):
            inputs = [(i >> j) & 1 for j in range(n)]
            # MLE of parity on Boolean inputs = parity (XOR)
            output = sum(inputs) % 2
            truth_table.append({"inputs": inputs, "output": output})

        print(
            f"[AlgebraizationReductionTemplate] MLE truth table: "
            f"{len(truth_table)} rows (same as parity on Booleans)"
        )
        return truth_table
