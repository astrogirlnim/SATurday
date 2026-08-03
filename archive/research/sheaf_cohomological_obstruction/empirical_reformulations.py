#!/usr/bin/env python3
"""
Test three reformulations of the sheaf construction for the P vs NP approach.

The original literal clause complex failed: H_1 was nonzero 100% of the time
at every ratio. This script tests three alternative constructions to find one
whose H_1 transitions at the SAT threshold.

Constructions tested:
  A. Conflict complex: vertices = clauses, edges = conflicting clause pairs,
     triangles = mutually conflicting triples. Motivation: directly models the
     local-to-global obstruction (two clauses cannot both be fully satisfied).

  B. Variable-clause incidence Laplacian rank: build the bipartite incidence graph
     between variables and clauses. Measure the number of independent cycles in
     the variable-clause neighborhood graph. Motivation: topological structure of
     the variable dependency hypergraph.

  C. Resolution graph: vertices = clauses, edge (c_i, c_j) if c_i and c_j can
     be resolved (share exactly one variable with opposite polarity). Triangles =
     triples with pairwise resolution edges. H_1 measures independent resolution
     cycle structure. Motivation: resolution is the canonical proof system for SAT.

Statistical adequacy:
  50 trials at n=20 is sufficient to conclude failure (H_1 = 1.00 everywhere is
  not a sampling artifact). For detecting a transition, we use:
    - n in {15, 20, 30} (threshold sharpens with n)
    - 100 trials per point (Wilson 95% CI width ~ ±10%)
    - Wilson confidence intervals printed for the key ratio band
  n=30 at high ratios may be slow for DPLL; we cap DPLL at 5000 recursive calls
  and mark timed-out instances separately.

Output:
  research/sheaf_cohomological_obstruction/logs/reformulations.jsonl
  Printed per-construction summary tables with CIs
"""

import sys, os, json, time, random, math
from typing import Optional

LOG_PATH = os.path.join(
    os.path.dirname(__file__), "logs", "reformulations.jsonl"
)
os.makedirs(os.path.dirname(LOG_PATH), exist_ok=True)

DPLL_LIMIT = 8000  # max recursive calls; None = unlimited


# ──────────────────────────────────────────────────────────────────────────────
# GF(2) Gaussian elimination (bit-packed, pure Python)
# ──────────────────────────────────────────────────────────────────────────────

def gf2_rank(num_rows: int, num_cols: int, col_sets: list) -> int:
    """Rank of (num_rows x num_cols) matrix over GF(2), column-sparse input."""
    if num_rows == 0 or num_cols == 0:
        return 0
    row_bits = [0] * num_rows
    for j, rows_with_1 in enumerate(col_sets):
        bit = 1 << j
        for i in rows_with_1:
            row_bits[i] ^= bit
    rank = 0
    pivot_row = 0
    for col in range(num_cols):
        bit = 1 << col
        found = next((r for r in range(pivot_row, num_rows) if row_bits[r] & bit), -1)
        if found == -1:
            continue
        row_bits[pivot_row], row_bits[found] = row_bits[found], row_bits[pivot_row]
        pv = row_bits[pivot_row]
        for r in range(num_rows):
            if r != pivot_row and (row_bits[r] & bit):
                row_bits[r] ^= pv
        rank += 1
        pivot_row += 1
    return rank


def h1_from_graph(num_verts: int, edges: list, triangles: list) -> int:
    """
    H_1(K; F_2) for a simplicial complex with given 1- and 2-skeleton.

    H_1 = ker(d_1) / im(d_2)
    dim H_1 = (|E| - rank(d_1)) - rank(d_2)
    """
    edge_list = sorted(set(tuple(sorted(e)) for e in edges))
    tri_list  = [tuple(sorted(t)) for t in triangles]
    edge_idx  = {e: i for i, e in enumerate(edge_list)}
    num_edges = len(edge_list)
    num_tris  = len(tri_list)

    if num_edges == 0:
        return 0

    # d_1: (num_verts x num_edges)
    d1_cols = [set() for _ in range(num_edges)]
    for j, (a, b) in enumerate(edge_list):
        d1_cols[j].add(a)
        d1_cols[j].add(b)

    # d_2: (num_edges x num_tris)
    d2_cols = [set() for _ in range(num_tris)]
    for j, (a, b, c) in enumerate(tri_list):
        d2_cols[j].add(edge_idx[tuple(sorted([a, b]))])
        d2_cols[j].add(edge_idx[tuple(sorted([b, c]))])
        d2_cols[j].add(edge_idx[tuple(sorted([a, c]))])

    rank_d1   = gf2_rank(num_verts, num_edges, d1_cols)
    rank_d2   = gf2_rank(num_edges, num_tris,  d2_cols)
    return max(0, (num_edges - rank_d1) - rank_d2)


# ──────────────────────────────────────────────────────────────────────────────
# Construction A: Conflict complex
# ──────────────────────────────────────────────────────────────────────────────

def compute_conflict_h1(n: int, clauses: list) -> int:
    """
    Conflict complex: vertices = clauses.
    Edge (i, j) if clause_i and clause_j share a variable with opposite polarity
    (i.e., they directly conflict on at least one variable).
    Triangle = three mutually conflicting clauses.

    Motivation: local-to-global obstruction: conflicting pairs cannot both be
    satisfied simultaneously. H_1 counts independent conflict cycles.
    """
    m = len(clauses)
    # Represent each clause as set of literals
    clause_lits = [set(c) for c in clauses]
    # Represent each clause as mapping var -> polarity
    clause_vars: list[dict] = [{abs(l): (1 if l > 0 else -1) for l in c} for c in clauses]

    def conflicts(i, j) -> bool:
        """True if clause i and j have at least one variable with opposite polarity."""
        for var, pol in clause_vars[i].items():
            if var in clause_vars[j] and clause_vars[j][var] != pol:
                return True
        return False

    edges = []
    adj = [set() for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            if conflicts(i, j):
                edges.append((i, j))
                adj[i].add(j)
                adj[j].add(i)

    triangles = []
    for i in range(m):
        nbrs = sorted(adj[i])
        for ki, j in enumerate(nbrs):
            if j <= i:
                continue
            for k in nbrs[ki + 1:]:
                if k > j and j in adj[i] and k in adj[i] and k in adj[j]:
                    triangles.append((i, j, k))

    return h1_from_graph(m, edges, triangles)


# ──────────────────────────────────────────────────────────────────────────────
# Construction B: Variable co-occurrence complex
# ──────────────────────────────────────────────────────────────────────────────

def compute_var_cooccurrence_h1(n: int, clauses: list) -> int:
    """
    Variable co-occurrence complex: vertices = variables 0..n-1.
    Edge (x, y) if variables x and y appear together in at least one clause.
    Triangle = three variables mutually co-occurring (all three pairs in some clause).

    Motivation: the topology of the variable dependency hypergraph. If variables
    are highly entangled in cycles, local assignment choices propagate globally.
    H_1 counts independent variable entanglement cycles.
    """
    # Vertices = variables (0-indexed)
    # For each clause, add edges on the three variable pairs
    edge_set: set = set()
    triangles = []

    for clause in clauses:
        vs = [abs(l) - 1 for l in clause]  # 0-indexed variable indices
        vs = sorted(set(vs))
        if len(vs) == 3:
            a, b, c = vs
            edge_set.add((a, b))
            edge_set.add((b, c))
            edge_set.add((a, c))
            triangles.append((a, b, c))
        elif len(vs) == 2:
            edge_set.add((vs[0], vs[1]))
        # len 1: skip (repeated variable in clause)

    return h1_from_graph(n, list(edge_set), triangles)


# ──────────────────────────────────────────────────────────────────────────────
# Construction C: Resolution complex
# ──────────────────────────────────────────────────────────────────────────────

def compute_resolution_h1(n: int, clauses: list) -> int:
    """
    Resolution complex: vertices = clauses.
    Edge (i, j) if clause_i and clause_j can be resolved: they share exactly one
    variable with opposite polarity (the resolvent literal). This mirrors the
    resolution proof system.
    Triangle = three clauses with pairwise resolution edges.

    Motivation: resolution is the canonical proof system for SAT. A formula
    requires a long resolution proof iff it is hard. H_1 measures independent
    resolution cycles that cannot be 'filled in' by a triangle of three clauses.
    Hard formulas near the threshold should require complex resolution structure.
    """
    m = len(clauses)
    clause_vars: list[dict] = [{abs(l): (1 if l > 0 else -1) for l in c} for c in clauses]

    def can_resolve(i, j) -> bool:
        """True if clauses i and j share exactly one variable with opposite polarity."""
        conflicts = sum(
            1 for var, pol in clause_vars[i].items()
            if var in clause_vars[j] and clause_vars[j][var] != pol
        )
        return conflicts == 1

    edges = []
    adj = [set() for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            if can_resolve(i, j):
                edges.append((i, j))
                adj[i].add(j)
                adj[j].add(i)

    triangles = []
    for i in range(m):
        nbrs = sorted(adj[i])
        for ki, j in enumerate(nbrs):
            if j <= i:
                continue
            for k in nbrs[ki + 1:]:
                if k > j and k in adj[i] and k in adj[j]:
                    triangles.append((i, j, k))

    return h1_from_graph(m, edges, triangles)


# ──────────────────────────────────────────────────────────────────────────────
# DPLL with call limit
# ──────────────────────────────────────────────────────────────────────────────

class DPLLLimitReached(Exception):
    pass

def is_satisfiable(n: int, clauses: list, limit: Optional[int] = DPLL_LIMIT):
    """DPLL with unit propagation and optional call limit.
    Returns (result: bool, timed_out: bool)."""
    calls = [0]

    def propagate(cls, assignment):
        changed = True
        while changed:
            changed = False
            new_cls = []
            for clause in cls:
                remaining = [l for l in clause if -l not in assignment]
                if not remaining:
                    return None
                if any(l in assignment for l in remaining):
                    continue
                if len(remaining) == 1:
                    assignment = assignment | {remaining[0]}
                    changed = True
                else:
                    new_cls.append(tuple(remaining))
            cls = new_cls
        return cls, assignment

    def solve(cls, assignment):
        if limit is not None:
            calls[0] += 1
            if calls[0] > limit:
                raise DPLLLimitReached()
        r = propagate(list(cls), frozenset(assignment))
        if r is None:
            return False
        cls, assignment = r
        if not cls:
            return True
        lit = cls[0][0]
        return solve(cls, assignment | {lit}) or solve(cls, assignment | {-lit})

    try:
        return solve(list(clauses), frozenset()), False
    except DPLLLimitReached:
        return False, True  # timeout: assume UNSAT for counting, flag separately


# ──────────────────────────────────────────────────────────────────────────────
# Statistics helpers
# ──────────────────────────────────────────────────────────────────────────────

def wilson_ci(k: int, n: int, z: float = 1.96) -> tuple[float, float]:
    """Wilson score 95% confidence interval for proportion k/n."""
    if n == 0:
        return 0.0, 0.0
    p = k / n
    center = (p + z**2 / (2 * n)) / (1 + z**2 / n)
    margin = (z / (1 + z**2 / n)) * math.sqrt(p * (1 - p) / n + z**2 / (4 * n**2))
    return max(0.0, center - margin), min(1.0, center + margin)


# ──────────────────────────────────────────────────────────────────────────────
# Instance generator
# ──────────────────────────────────────────────────────────────────────────────

def generate_3sat(n: int, m: int, seed: int) -> list:
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        clauses.append(tuple(v * rng.choice([1, -1]) for v in vs))
    return clauses


# ──────────────────────────────────────────────────────────────────────────────
# Experiment configuration
# ──────────────────────────────────────────────────────────────────────────────

CONSTRUCTIONS = {
    "A_conflict":         compute_conflict_h1,
    "B_var_cooccurrence": compute_var_cooccurrence_h1,
    "C_resolution":       compute_resolution_h1,
}

CONFIG = {
    "n_values":           [15, 20, 30],
    "ratios": [
        2.5, 3.0, 3.5, 3.8, 4.0, 4.1, 4.2, 4.267,
        4.3, 4.4, 4.6, 5.0, 5.5, 6.0,
    ],
    "trials_per_point":   100,
}


# ──────────────────────────────────────────────────────────────────────────────
# Runner
# ──────────────────────────────────────────────────────────────────────────────

def run():
    print()
    print("=" * 76)
    print("SHEAF H_1 REFORMULATION EXPERIMENT  (3 constructions)")
    print("100 trials per point | Wilson 95% CI | n in {15, 20, 30}")
    print("=" * 76)
    print()
    print("Statistical note: 50 trials was sufficient to conclude the literal")
    print("clause complex fails (H_1>0 = 1.00 everywhere is definitive).")
    print("100 trials at n=30 gives Wilson CI width ~±10% to locate transitions.")
    print()

    # results[construction][n][ratio] = {sat_frac, h1_nonzero_frac, h1_mean, ...}
    results: dict = {c: {n: {} for n in CONFIG["n_values"]} for c in CONSTRUCTIONS}

    for n in CONFIG["n_values"]:
        t_start = time.time()
        print(f"{'='*76}")
        print(f"n = {n}")
        print(f"{'='*76}")
        print(f"{'ratio':>7}  {'SAT frac (CI)':>22}  {'A_conflict H1>0':>16}  {'B_varco H1>0':>13}  {'C_resol H1>0':>13}")
        print("-" * 76)

        for ratio in CONFIG["ratios"]:
            m = round(ratio * n)
            T = CONFIG["trials_per_point"]

            sat_count   = 0
            timeout_count = 0
            h1_counts   = {c: 0 for c in CONSTRUCTIONS}
            h1_sums     = {c: 0 for c in CONSTRUCTIONS}

            for trial in range(T):
                seed = n * 10**7 + int(ratio * 1000) * 1000 + trial
                clauses = generate_3sat(n, m, seed)

                sat, timed_out = is_satisfiable(n, clauses)
                if sat:
                    sat_count += 1
                if timed_out:
                    timeout_count += 1

                h1_vals = {}
                for cname, cfn in CONSTRUCTIONS.items():
                    h1 = cfn(n, clauses)
                    h1_vals[cname] = h1
                    h1_sums[cname] += h1
                    if h1 > 0:
                        h1_counts[cname] += 1

                with open(LOG_PATH, "a") as f:
                    f.write(json.dumps({
                        "n": n, "m": m, "ratio": ratio, "trial": trial,
                        "sat": sat, "timed_out": timed_out,
                        "h1": h1_vals,
                        "timestamp": int(time.time()),
                    }) + "\n")

            sat_lo, sat_hi = wilson_ci(sat_count, T)
            sat_str = f"{sat_count/T:.2f} [{sat_lo:.2f},{sat_hi:.2f}]"
            h1_strs = {
                c: f"{h1_counts[c]/T:.2f}" for c in CONSTRUCTIONS
            }
            timeout_str = f" (timeout={timeout_count})" if timeout_count else ""
            marker = "  <--" if abs(ratio - 4.267) < 0.01 else ""

            print(f"{ratio:>7.3f}  {sat_str:>22}  {h1_strs['A_conflict']:>16}  "
                  f"{h1_strs['B_var_cooccurrence']:>13}  "
                  f"{h1_strs['C_resolution']:>13}{timeout_str}{marker}")

            for cname in CONSTRUCTIONS:
                results[cname][n][ratio] = {
                    "sat_frac":          sat_count / T,
                    "h1_nonzero_frac":   h1_counts[cname] / T,
                    "h1_mean":           h1_sums[cname] / T,
                    "sat_ci":            (sat_lo, sat_hi),
                    "timeout_frac":      timeout_count / T,
                }

        print(f"[done in {time.time() - t_start:.1f}s]\n")

    # Per-construction verdict
    print("=" * 76)
    print("VERDICT BY CONSTRUCTION")
    print("=" * 76)
    for cname in CONSTRUCTIONS:
        assess(cname, results[cname])

    print()
    print(f"Results logged to: {LOG_PATH}")


def assess(name: str, results_by_n: dict):
    n = max(results_by_n.keys())
    data = results_by_n[n]
    ratios = sorted(data.keys())

    sat_transition = next((r for r in ratios if data[r]["sat_frac"] < 0.5), None)
    h1_transition  = next((r for r in ratios if data[r]["h1_nonzero_frac"] > 0.5), None)
    h1_always_on   = all(data[r]["h1_nonzero_frac"] >= 0.98 for r in ratios)
    h1_always_off  = all(data[r]["h1_nonzero_frac"] <= 0.02 for r in ratios)

    print(f"\nConstruction {name}  (n={n})")
    print(f"  SAT transition (< 50%):     ratio ~ {sat_transition}")
    print(f"  H_1 transition (> 50%):     ratio ~ {h1_transition}")

    if h1_always_on:
        print(f"  VERDICT: FAIL -- H_1 > 0 always. Same failure as literal clause complex.")
    elif h1_always_off:
        print(f"  VERDICT: FAIL -- H_1 = 0 always. Trivial invariant.")
    elif sat_transition and h1_transition and abs(sat_transition - h1_transition) <= 0.5:
        print(f"  VERDICT: PROMISING -- H_1 transitions within 0.5 of SAT threshold.")
        print(f"  Recommend: increase n and trials, pursue formal sheaf definition.")
    elif sat_transition and h1_transition:
        gap = abs(sat_transition - h1_transition)
        print(f"  VERDICT: INCONSISTENT -- transitions separated by {gap:.2f}.")
        print(f"  H_1 invariant does not track satisfiability threshold at this scale.")
    else:
        print(f"  VERDICT: INCONCLUSIVE -- transition not clearly visible.")


if __name__ == "__main__":
    run()
