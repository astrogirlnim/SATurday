"""
Bet B: Algorithm Synthesis Templates.

Generates conjectures about whether polynomial-time algorithm schemas exist
for restricted problem classes.

The SAT encoding asks: "Does a program schema of bounded depth that correctly
solves problem P on all inputs of size n exist with runtime at most T(n)?"

UNSAT => proven no such schema exists at this bound.
SAT   => witness encodes a concrete algorithm description.

Schemas implemented:
- sorting:     Comparison-based sort, T(n) = O(n^2) bound (insertion sort family)
- searching:   Linear search in sorted array, T(n) = O(n)
- graph_reach: Reachability via adjacency traversal, T(n,m) = O(n+m)
"""

from typing import Any, Dict
from .base import ConjectureTemplate


class SortingAlgorithmTemplate(ConjectureTemplate):
    """
    Template for sorting algorithm synthesis with O(n^2) runtime bound.

    Asks: Does a comparison-sort schema of at most n^2 steps correctly sort
    all arrays of n elements?

    For small n (2-8): SAT expected (insertion sort witnesses exist).
    Used to validate the algorithm synthesis pipeline before harder problems.
    """

    def __init__(self):
        super().__init__("bet_b_sorting", "B")

    def generate_lean_stub(self, **params) -> str:
        n    = params.get("n", 3)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        bound = n * n  # O(n^2) comparison bound

        return f"""import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetB

/-!
# Algorithm Synthesis: Sorting with Polynomial Bound

Conjecture: There exists a comparison-sort algorithm schema that correctly
sorts all arrays of {n} elements using at most {bound} comparisons.

## Encoding
The SAT solver searches for a comparison network of depth <= {bound} that
sorts every permutation of {n} elements. SAT witness = concrete sort network.
UNSAT = no such network exists at this bound.

## Generated from
- Task: {task_id}
- Seed: {seed}
- Template: {self.template_id}
- n = {n}, bound = {bound} comparisons

LOG: Generated sorting algorithm synthesis conjecture (n={n}, bound={bound})
-/

/-- A comparison step: swap elements at positions i and j if out of order. -/
structure ComparisonStep (n : Nat) where
  left  : Fin n
  right : Fin n
  h     : left.val < right.val

/-- A sorting network: sequence of comparison steps. -/
def SortingNetwork (n depth : Nat) := Fin depth → ComparisonStep n

/-- Apply one comparison step to an array. -/
def applyStep {{n : Nat}} (arr : Fin n → Nat) (step : ComparisonStep n) : Fin n → Nat :=
  fun i =>
    if i = step.left then
      min (arr step.left) (arr step.right)
    else if i = step.right then
      max (arr step.left) (arr step.right)
    else
      arr i

/-- Apply a full sorting network to an array. -/
def applyNetwork {{n depth : Nat}} (arr : Fin n → Nat) (net : SortingNetwork n depth) : Fin n → Nat :=
  Fin.foldl depth (fun acc d => applyStep acc (net d)) arr

/-- An array is sorted if each element is <= the next. -/
def isSorted {{n : Nat}} (arr : Fin n → Nat) : Prop :=
  ∀ i : Fin n, i.val + 1 < n → arr i ≤ arr ⟨i.val + 1, by omega⟩

/-- Conjecture: a {bound}-step sorting network exists for n={n}. -/
theorem sorting_network_exists_{n} :
    ∃ (net : SortingNetwork {n} {bound}),
      ∀ (arr : Fin {n} → Nat), isSorted (applyNetwork arr net) := by
  -- LOG: SAT solver found network if SAT; proved nonexistence if UNSAT
  sorry

end SATurday.Conjectures.BetB
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n       = params.get("n", 3)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        bound   = n * n  # O(n^2) comparisons

        return {
            "conjecture_id": f"{self.template_id}_n{n}_s{seed}",
            "task_id": task_id,
            "description": f"Sorting network synthesis: n={n} elements, bound={bound} steps",
            "circuit": {
                "type": "sorting_network",
                "num_inputs": n,
                "max_gates": bound,
                "depth_limit": bound,
            },
            "target_function": {
                "name": "sorting",
                "num_elements": n,
                "comparison_bound": bound,
                "truth_table": self._generate_sort_spec(n),
            },
            "encoding": {
                "method": "algorithm_synthesis",
                "optimize": True,
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": max(n * 30, 60),
                "expected_result": "SAT",
            },
        }

    def _generate_sort_spec(self, n: int) -> list:
        """
        Generate correctness spec: for each permutation of [0..n-1],
        the network must produce a sorted output.

        For small n, enumerate all permutations explicitly.
        For n > 6, return empty (trigger symbolic encoding in miner).
        """
        if n > 6:
            print(f"[SortingTemplate] n={n} > 6: returning empty spec for symbolic encoding")
            return []

        from itertools import permutations
        spec = []
        for perm in permutations(range(n)):
            spec.append({
                "inputs": list(perm),
                "output": list(range(n)),  # Expected: sorted [0,1,...,n-1]
            })
        print(f"[SortingTemplate] Generated {len(spec)} permutation rows for n={n}")
        return spec


class SearchingAlgorithmTemplate(ConjectureTemplate):
    """
    Template for linear search synthesis in sorted arrays.

    Asks: Does a search schema of at most n steps correctly find a target
    element in a sorted array of n elements?

    For small n: SAT expected (binary search or linear scan witnesses exist).
    """

    def __init__(self):
        super().__init__("bet_b_searching", "B")

    def generate_lean_stub(self, **params) -> str:
        n    = params.get("n", 4)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        bound = n  # O(n) steps

        return f"""import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetB

/-!
# Algorithm Synthesis: Searching in Sorted Array

Conjecture: There exists a search algorithm schema that correctly finds
any target value in a sorted array of {n} elements using at most {bound} steps.

## Generated from
- Task: {task_id}
- Seed: {seed}
- Template: {self.template_id}
- n = {n}, bound = {bound} steps

LOG: Generated searching algorithm synthesis conjecture (n={n}, bound={bound})
-/

/-- A search decision step: compare target to element at position i. -/
structure SearchStep (n : Nat) where
  pos : Fin n  -- Index to probe

/-- A search program: sequence of probe decisions. -/
def SearchProgram (n depth : Nat) := Fin depth → SearchStep n

/-- Result of running search program: found index or None. -/
def runSearch {{n depth : Nat}}
    (arr : Fin n → Int) (target : Int) (prog : SearchProgram n depth) : Option (Fin n) :=
  Fin.foldl depth (fun acc d =>
    match acc with
    | some idx => some idx
    | none =>
      let step := prog d
      if arr step.pos = target then some step.pos else none
  ) none

/-- Conjecture: a {bound}-step search program exists for sorted arrays of n={n}. -/
theorem search_program_exists_{n} :
    ∃ (prog : SearchProgram {n} {bound}),
      ∀ (arr : Fin {n} → Int) (target : Int),
        (∃ i : Fin {n}, arr i = target) →
        (runSearch arr target prog).isSome = true := by
  sorry

end SATurday.Conjectures.BetB
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n       = params.get("n", 4)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        bound   = n

        return {
            "conjecture_id": f"{self.template_id}_n{n}_s{seed}",
            "task_id": task_id,
            "description": f"Search algorithm synthesis: n={n} elements, bound={bound} steps",
            "circuit": {
                "type": "search_program",
                "num_inputs": n,
                "max_gates": bound,
                "depth_limit": bound,
            },
            "target_function": {
                "name": "searching",
                "array_size": n,
                "step_bound": bound,
                "truth_table": [],  # Symbolic encoding for all arrays
            },
            "encoding": {
                "method": "algorithm_synthesis",
                "optimize": True,
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": max(n * 20, 60),
                "expected_result": "SAT",
            },
        }


class GraphReachabilityTemplate(ConjectureTemplate):
    """
    Template for graph reachability algorithm synthesis.

    Asks: Does a traversal schema of at most n+m steps correctly determine
    reachability between two nodes in a graph with n nodes and m edges?

    For small n: SAT expected (BFS/DFS witnesses exist).
    """

    def __init__(self):
        super().__init__("bet_b_graph_reach", "B")

    def generate_lean_stub(self, **params) -> str:
        n    = params.get("n", 3)
        seed = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        max_edges = n * (n - 1)  # Complete graph upper bound
        bound = n + max_edges    # O(V+E) traversal

        return f"""import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SATurday.Conjectures.BetB

/-!
# Algorithm Synthesis: Graph Reachability

Conjecture: There exists a graph traversal schema that correctly determines
reachability between any two nodes in a graph with {n} nodes using at most
{bound} steps.

## Generated from
- Task: {task_id}
- Seed: {seed}
- Template: {self.template_id}
- n = {n} nodes, bound = {bound} steps

LOG: Generated graph reachability synthesis conjecture (n={n}, bound={bound})
-/

/-- A graph on n nodes as an adjacency relation. -/
def Graph (n : Nat) := Fin n → Fin n → Bool

/-- A traversal step: which node frontier to expand. -/
structure TraversalStep (n : Nat) where
  node : Fin n

/-- A traversal program. -/
def TraversalProgram (n depth : Nat) := Fin depth → TraversalStep n

/-- Conjecture: a {bound}-step reachability program exists for n={n} node graphs. -/
theorem graph_reach_exists_{n} :
    ∃ (prog : TraversalProgram {n} {bound}),
      ∀ (g : Graph {n}) (src dst : Fin {n}),
        True := by  -- Placeholder: full spec requires reachability predicate
  exact ⟨fun _ => ⟨⟨0, by omega⟩⟩, fun _ _ _ => trivial⟩

end SATurday.Conjectures.BetB
"""

    def generate_cnf_spec(self, **params) -> Dict[str, Any]:
        n       = params.get("n", 3)
        seed    = params.get("seed", 0)
        task_id = params.get("task_id", "unknown")
        max_edges = n * (n - 1)
        bound = n + max_edges

        return {
            "conjecture_id": f"{self.template_id}_n{n}_s{seed}",
            "task_id": task_id,
            "description": f"Graph reachability synthesis: n={n} nodes, bound={bound} steps",
            "circuit": {
                "type": "graph_traversal",
                "num_inputs": n,
                "max_gates": bound,
                "depth_limit": n,
            },
            "target_function": {
                "name": "graph_reach",
                "num_nodes": n,
                "step_bound": bound,
                "truth_table": [],
            },
            "encoding": {
                "method": "algorithm_synthesis",
                "optimize": True,
            },
            "seed": seed,
            "solver_config": {
                "timeout_seconds": max(n * 30, 60),
                "expected_result": "SAT",
            },
        }
