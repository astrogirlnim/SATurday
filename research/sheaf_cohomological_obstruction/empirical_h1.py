#!/usr/bin/env python3
"""
Empirical H_1 computation for random 3-SAT instances near the satisfiability threshold.

Core conjecture being tested:
  Does the H_1 transition of the literal clause complex coincide with
  the satisfiability threshold at ratio approximately 4.267 clauses/variable?

If yes: the cohomological invariant tracks hardness, validating the approach.
If no: the conjecture as stated is wrong and the approach needs reformulation.

Method:
  For each (n, ratio, trial):
  1. Generate random 3-SAT instance: n variables, m = round(ratio * n) clauses
  2. Build the literal clause complex K:
       Vertices  = literals {x_1,...,x_n, ~x_1,...,~x_n}  (2n vertices)
       2-simplices = clauses (each clause is a triangle on 3 literals)
       1-skeleton = all pairs of literals co-occurring in some clause
  3. Compute dim H_1(K; F_2) via Gaussian elimination over GF(2), pure Python
  4. Check satisfiability via built-in DPLL
  5. Log to JSONL and print summary table
"""

import sys, os, json, time, random
from typing import Optional

LOG_PATH = os.path.join(os.path.dirname(__file__), "logs", "h1_empirical.jsonl")
os.makedirs(os.path.dirname(LOG_PATH), exist_ok=True)

print("[init] SAT solver: built-in DPLL")
print("[init] GF(2) linear algebra: pure Python (bit-packed rows)")
print()


# ──────────────────────────────────────────────────────────────────────────────
# GF(2) Gaussian elimination (bit-packed, pure Python)
# ──────────────────────────────────────────────────────────────────────────────

def gf2_rank(num_rows: int, num_cols: int, col_sets: list[set]) -> int:
    """
    Compute rank of a (num_rows x num_cols) matrix over GF(2).

    col_sets[j] = set of row indices where column j has a 1.
    This is a column-major sparse representation.

    We transpose to row-major for elimination:
      row_bits[i] = integer bitmask of which columns are set in row i.
    """
    if num_rows == 0 or num_cols == 0:
        return 0

    # Build row bitmasks
    row_bits = [0] * num_rows
    for j, rows_with_1 in enumerate(col_sets):
        for i in rows_with_1:
            row_bits[i] ^= (1 << j)

    rank = 0
    pivot_row = 0
    for col in range(num_cols):
        bit = 1 << col
        # Find a row at or below pivot_row that has bit set
        found = -1
        for r in range(pivot_row, num_rows):
            if row_bits[r] & bit:
                found = r
                break
        if found == -1:
            continue
        # Swap
        row_bits[pivot_row], row_bits[found] = row_bits[found], row_bits[pivot_row]
        # Eliminate all other rows
        for r in range(num_rows):
            if r != pivot_row and (row_bits[r] & bit):
                row_bits[r] ^= row_bits[pivot_row]
        rank += 1
        pivot_row += 1

    return rank


# ──────────────────────────────────────────────────────────────────────────────
# H_1 computation
# ──────────────────────────────────────────────────────────────────────────────

def literal_index(lit: int, n: int) -> int:
    return (lit - 1) if lit > 0 else (n + (-lit) - 1)


def compute_h1(n: int, clauses: list) -> int:
    """
    Compute dim H_1(K; F_2) for the literal clause complex K.

    H_1 = ker(d_1) / im(d_2)
    dim H_1 = (|E| - rank(d_1)) - rank(d_2)
    """
    num_verts = 2 * n
    edge_set: set[tuple] = set()
    triangles: list[tuple] = []

    for clause in clauses:
        a, b, c = (literal_index(lit, n) for lit in clause)
        tri = tuple(sorted([a, b, c]))
        triangles.append(tri)
        edge_set.add(tuple(sorted([a, b])))
        edge_set.add(tuple(sorted([b, c])))
        edge_set.add(tuple(sorted([a, c])))

    edges = sorted(edge_set)
    edge_idx = {e: i for i, e in enumerate(edges)}
    num_edges = len(edges)
    num_tris = len(triangles)

    # d_1: (num_verts x num_edges) — column j has 1s at rows a and b for edge (a,b)
    d1_col_sets = [set() for _ in range(num_edges)]
    for j, (a, b) in enumerate(edges):
        d1_col_sets[j].add(a)
        d1_col_sets[j].add(b)

    # d_2: (num_edges x num_tris) — column j has 1s at the three edges of triangle j
    d2_col_sets = [set() for _ in range(num_tris)]
    for j, (a, b, c) in enumerate(triangles):
        d2_col_sets[j].add(edge_idx[tuple(sorted([a, b]))])
        d2_col_sets[j].add(edge_idx[tuple(sorted([b, c]))])
        d2_col_sets[j].add(edge_idx[tuple(sorted([a, c]))])

    rank_d1 = gf2_rank(num_verts, num_edges, d1_col_sets)
    rank_d2 = gf2_rank(num_edges, num_tris, d2_col_sets)

    dim_ker_d1 = num_edges - rank_d1
    return max(0, dim_ker_d1 - rank_d2)


# ──────────────────────────────────────────────────────────────────────────────
# Built-in DPLL solver
# ──────────────────────────────────────────────────────────────────────────────

def is_satisfiable(n: int, clauses: list) -> bool:
    """DPLL with unit propagation."""

    def propagate(cls, assignment):
        changed = True
        while changed:
            changed = False
            new_cls = []
            for clause in cls:
                remaining = [lit for lit in clause if -lit not in assignment]
                if not remaining:
                    return None  # conflict
                if any(lit in assignment for lit in remaining):
                    continue    # satisfied
                if len(remaining) == 1:
                    lit = remaining[0]
                    assignment = assignment | {lit}
                    changed = True
                else:
                    new_cls.append(tuple(remaining))
            cls = new_cls
        return cls, assignment

    def solve(cls, assignment):
        r = propagate(list(cls), frozenset(assignment))
        if r is None:
            return False
        cls, assignment = r
        if not cls:
            return True
        # Branch on first literal of first clause
        lit = cls[0][0]
        return solve(cls, assignment | {lit}) or solve(cls, assignment | {-lit})

    return solve(list(clauses), frozenset())


# ──────────────────────────────────────────────────────────────────────────────
# Instance generator
# ──────────────────────────────────────────────────────────────────────────────

def generate_3sat(n: int, m: int, seed: int) -> list:
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        vars_ = rng.sample(range(1, n + 1), 3)
        clause = tuple(v * rng.choice([1, -1]) for v in vars_)
        clauses.append(clause)
    return clauses


# ──────────────────────────────────────────────────────────────────────────────
# Experiment configuration
# ──────────────────────────────────────────────────────────────────────────────

EXPERIMENT_CONFIG = {
    "n_values": [10, 15, 20],
    "ratios": [
        2.5, 3.0, 3.5, 3.8, 4.0, 4.1, 4.2, 4.267,
        4.3, 4.4, 4.6, 5.0, 5.5, 6.0,
    ],
    "trials_per_point": 50,
}


# ──────────────────────────────────────────────────────────────────────────────
# Runner
# ──────────────────────────────────────────────────────────────────────────────

def run_experiments():
    print("=" * 72)
    print("SHEAF H_1 EMPIRICAL EXPERIMENT")
    print("Conjecture: H_1 transition coincides with SAT threshold ~4.267")
    print("=" * 72)
    print()

    results: dict = {}

    for n in EXPERIMENT_CONFIG["n_values"]:
        results[n] = {}
        t_total = time.time()
        print(f"[n={n}] {len(EXPERIMENT_CONFIG['ratios'])} ratios x "
              f"{EXPERIMENT_CONFIG['trials_per_point']} trials ...")

        for ratio in EXPERIMENT_CONFIG["ratios"]:
            m = round(ratio * n)
            sat_count = 0
            h1_sum = 0
            h1_nonzero = 0

            for trial in range(EXPERIMENT_CONFIG["trials_per_point"]):
                seed = n * 100000 + int(ratio * 1000) * 100 + trial
                clauses = generate_3sat(n, m, seed)

                t0 = time.time()
                sat = is_satisfiable(n, clauses)
                h1 = compute_h1(n, clauses)
                elapsed = time.time() - t0

                if sat:
                    sat_count += 1
                h1_sum += h1
                if h1 > 0:
                    h1_nonzero += 1

                with open(LOG_PATH, "a") as f:
                    f.write(json.dumps({
                        "n": n, "m": m, "ratio": ratio, "trial": trial,
                        "sat": sat, "dim_h1": h1,
                        "elapsed_s": round(elapsed, 4),
                        "timestamp": int(time.time()),
                    }) + "\n")

            T = EXPERIMENT_CONFIG["trials_per_point"]
            sat_frac     = sat_count / T
            h1_mean      = h1_sum / T
            h1_frac      = h1_nonzero / T
            results[n][ratio] = {
                "sat_frac": sat_frac,
                "h1_mean":  h1_mean,
                "h1_nonzero_frac": h1_frac,
            }

            marker = "  <-- threshold" if abs(ratio - 4.267) < 0.01 else ""
            print(f"  ratio={ratio:.3f}  m={m:3d}  "
                  f"SAT={sat_frac:.2f}  "
                  f"H1_mean={h1_mean:5.2f}  "
                  f"H1>0={h1_frac:.2f}{marker}")

        print(f"  [done in {time.time() - t_total:.1f}s]\n")

    print_summary(results)
    assess_conjecture(results)


def print_summary(results: dict):
    ns = EXPERIMENT_CONFIG["n_values"]
    ratios = EXPERIMENT_CONFIG["ratios"]

    print("=" * 72)
    print("SUMMARY TABLE  (SAT frac | H_1>0 frac)")
    print("=" * 72)
    hdr = f"{'ratio':>7} |"
    for n in ns:
        hdr += f"  n={n:2d} SAT  H1>0 |"
    print(hdr)
    print("-" * len(hdr))
    for ratio in ratios:
        row = f"{ratio:>7.3f} |"
        for n in ns:
            r = results[n][ratio]
            row += f"  {r['sat_frac']:.2f}    {r['h1_nonzero_frac']:.2f}  |"
        if abs(ratio - 4.267) < 0.01:
            row += "  <-- SAT threshold"
        print(row)
    print()


def assess_conjecture(results: dict):
    n = max(results.keys())
    data = results[n]
    ratios = sorted(data.keys())

    sat_transition = next(
        (r for r in ratios if data[r]["sat_frac"] < 0.5), None
    )
    h1_transition = next(
        (r for r in ratios if data[r]["h1_nonzero_frac"] > 0.5), None
    )

    print("=" * 72)
    print(f"CONJECTURE VERDICT  (n={n})")
    print("=" * 72)
    print(f"SAT transition (SAT < 50%):  ratio ~ {sat_transition}")
    print(f"H_1 transition (H_1>0 > 50%): ratio ~ {h1_transition}")
    print()

    if sat_transition is not None and h1_transition is not None:
        gap = abs(sat_transition - h1_transition)
        if gap <= 0.4:
            print("VERDICT: CONSISTENT")
            print("H_1 transition roughly aligns with the SAT threshold.")
            print("Conjecture is empirically supported at this scale.")
            print("Recommendation: proceed to formal Lean development.")
        else:
            print("VERDICT: INCONSISTENT")
            print(f"H_1 transition (ratio {h1_transition}) is far from "
                  f"SAT threshold (ratio {sat_transition}) by {gap:.3f}.")
            print("The literal clause complex does not capture the hardness transition.")
            print("Recommendation: reformulate the sheaf construction before Lean work.")
    else:
        print("VERDICT: INCONCLUSIVE")
        print("Transitions not clearly visible at this scale.")

    print()
    print(f"Results logged to: {LOG_PATH}")


if __name__ == "__main__":
    run_experiments()
