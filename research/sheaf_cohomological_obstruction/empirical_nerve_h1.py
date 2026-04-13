#!/usr/bin/env python3
"""
Cech H_1 of the clause cover nerve: empirical test for 2-SAT and 3-SAT.

Candidate construction (c) from notes/linearization.md:

  Each clause C_i defines an open set U_i of partial assignments consistent
  with C_i. The nerve N of the cover {U_i} has:
    Vertices  = clauses
    Edge (i,j) iff U_i and U_j have a common consistent partial assignment
              (equivalently: clauses C_i and C_j are simultaneously satisfiable)
    Triangle (i,j,k) iff U_i, U_j, U_k are mutually simultaneously satisfiable

  H_1(N; F_2) measures independent obstruction cycles in the clause cover.

Hypothesis: H_1(N; F_2) != 0 iff the formula is UNSATISFIABLE.

If true for 2-SAT: this is the correct obstruction construction and a natural
candidate for formal Lean development. If false: candidate (b) (relative cohomology)
must be investigated instead.

The test is cheap: nerve construction is O(m^2) per instance, H_1 via GF(2)
rank is O(m^3) in the worst case. 2-SAT satisfiability is O(n+m) via SCC.

Output: research/sheaf_cohomological_obstruction/logs/nerve_h1.jsonl
"""

import sys, os, json, time, random, math
from typing import Optional

LOG_PATH = os.path.join(os.path.dirname(__file__), "logs", "nerve_h1.jsonl")
os.makedirs(os.path.dirname(LOG_PATH), exist_ok=True)

print("[init] Clause cover nerve H_1 experiment")
print("[init] Hypothesis: H_1(nerve) != 0 iff UNSAT")
print()


# ── GF(2) rank (reused from earlier empirical scripts) ────────────────────────

def gf2_rank(num_rows: int, num_cols: int, col_sets: list) -> int:
    if num_rows == 0 or num_cols == 0:
        return 0
    row_bits = [0] * num_rows
    for j, rows in enumerate(col_sets):
        bit = 1 << j
        for i in rows:
            row_bits[i] ^= bit
    rank, pivot = 0, 0
    for col in range(num_cols):
        bit = 1 << col
        found = next((r for r in range(pivot, num_rows) if row_bits[r] & bit), -1)
        if found == -1:
            continue
        row_bits[pivot], row_bits[found] = row_bits[found], row_bits[pivot]
        pv = row_bits[pivot]
        for r in range(num_rows):
            if r != pivot and row_bits[r] & bit:
                row_bits[r] ^= pv
        rank += 1
        pivot += 1
    return rank


def h1_from_graph(num_verts: int, edges: list, triangles: list) -> int:
    edge_list = sorted(set(tuple(sorted(e)) for e in edges))
    tri_list  = [tuple(sorted(t)) for t in triangles]
    edge_idx  = {e: i for i, e in enumerate(edge_list)}
    E, T = len(edge_list), len(tri_list)
    if E == 0:
        return 0
    d1_cols = [{a, b} for a, b in edge_list]
    d2_cols = [
        {edge_idx[tuple(sorted([a, b]))],
         edge_idx[tuple(sorted([b, c]))],
         edge_idx[tuple(sorted([a, c]))]}
        for a, b, c in tri_list
    ]
    rank_d1 = gf2_rank(num_verts, E, d1_cols)
    rank_d2 = gf2_rank(E, T, d2_cols) if T else 0
    return max(0, (E - rank_d1) - rank_d2)


# ── Clause compatibility ───────────────────────────────────────────────────────

def clauses_compatible(ci: tuple, cj: tuple) -> bool:
    """
    True iff clauses ci and cj can be simultaneously satisfied by some assignment.
    Two clauses are incompatible iff one requires x=1 and x=0 for every variable,
    i.e., for every variable in ci there is a conflicting literal in cj that covers
    all satisfying assignments of ci. In practice: incompatible iff for every literal
    in ci, its negation is in cj AND len(ci) = len(cj) = 1 (unit clauses only).
    Actually: two clauses are simultaneously satisfiable unless one clause is the
    set of negations of all literals in the other -- i.e., they are a 'resolution
    pair' where every literal is covered. For general k-SAT this is complex; for
    2-SAT it is: (a or b) and (~a or ~b) are compatible (set a=0, b=1 satisfies both).
    The incompatible case for two clauses ci, cj is:
      for EVERY literal l in ci, ~l is in cj  (i.e., cj subsumes all negations of ci).
    This means any assignment satisfying ci falsifies every literal in cj.
    """
    lits_ci = set(ci)
    neg_ci  = {-l for l in lits_ci}
    lits_cj = set(cj)
    # Incompatible: cj contains the negation of every literal in ci
    return not neg_ci.issubset(lits_cj)


def triples_compatible(ci: tuple, cj: tuple, ck: tuple) -> bool:
    """True iff all three clauses can be simultaneously satisfied."""
    # Build a small DPLL over just these clauses
    clauses = [list(ci), list(cj), list(ck)]
    return _dpll_small(clauses, {})


def _dpll_small(clauses: list, assignment: dict) -> bool:
    """Minimal DPLL for small clause sets (for triple compatibility check)."""
    clauses = [
        [l for l in c if assignment.get(abs(l)) is None]
        for c in clauses
        if not any(
            (l > 0 and assignment.get(l) is True) or
            (l < 0 and assignment.get(-l) is False)
            for l in c
        )
    ]
    if any(len(c) == 0 for c in clauses):
        return False
    if not clauses:
        return True
    # Unit propagation
    for c in clauses:
        if len(c) == 1:
            lit = c[0]
            new_assign = dict(assignment)
            new_assign[abs(lit)] = (lit > 0)
            return _dpll_small(clauses, new_assign)
    # Branch
    lit = clauses[0][0]
    a1 = dict(assignment); a1[abs(lit)] = (lit > 0)
    a2 = dict(assignment); a2[abs(lit)] = (lit < 0)
    return _dpll_small(clauses, a1) or _dpll_small(clauses, a2)


# ── Nerve construction ─────────────────────────────────────────────────────────

def compute_nerve_h1(n: int, clauses: list) -> int:
    """
    Build the nerve of the clause cover and compute H_1(nerve; F_2).

    Vertices = clause indices 0..m-1.
    Edge (i,j) if clauses i and j are simultaneously satisfiable.
    Triangle (i,j,k) if all three are simultaneously satisfiable.
    """
    m = len(clauses)
    compat = [[False] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            compat[i][j] = compat[j][i] = clauses_compatible(clauses[i], clauses[j])

    edges = [(i, j) for i in range(m) for j in range(i+1, m) if compat[i][j]]

    triangles = []
    adj = [set() for _ in range(m)]
    for i, j in edges:
        adj[i].add(j); adj[j].add(i)
    for i in range(m):
        nbrs = sorted(adj[i])
        for ki, j in enumerate(nbrs):
            if j <= i:
                continue
            for k in nbrs[ki+1:]:
                if k > j and k in adj[i] and k in adj[j]:
                    if triples_compatible(clauses[i], clauses[j], clauses[k]):
                        triangles.append((i, j, k))

    return h1_from_graph(m, edges, triangles)


# ── 2-SAT solver via implication graph SCC ────────────────────────────────────

def is_2sat(n: int, clauses: list) -> bool:
    """
    O(n+m) 2-SAT solver via Kosaraju SCC.
    Variable i (1-indexed) -> node 2*(i-1); negation -> node 2*(i-1)+1.
    """
    N = 2 * n
    graph  = [[] for _ in range(N)]
    rgraph = [[] for _ in range(N)]

    def lit_node(l):
        return 2*(abs(l)-1) + (0 if l > 0 else 1)

    def neg_node(v):
        return v ^ 1

    for clause in clauses:
        if len(clause) != 2:
            # Fall back to DPLL for non-2-clauses (shouldn't happen in 2-SAT test)
            return _dpll_small([list(c) for c in clauses], {})
        a, b = clause
        na, nb = lit_node(a), lit_node(b)
        graph[neg_node(na)].append(nb)
        graph[neg_node(nb)].append(na)
        rgraph[nb].append(neg_node(na))
        rgraph[na].append(neg_node(nb))

    visited = [False] * N
    order   = []

    def dfs1(v):
        stack = [(v, 0)]
        while stack:
            u, state = stack.pop()
            if state == 0:
                if visited[u]:
                    continue
                visited[u] = True
                stack.append((u, 1))
                for w in graph[u]:
                    if not visited[w]:
                        stack.append((w, 0))
            else:
                order.append(u)

    for v in range(N):
        if not visited[v]:
            dfs1(v)

    comp    = [-1] * N
    c_id    = [0]

    def dfs2(v, c):
        stack = [v]
        while stack:
            u = stack.pop()
            if comp[u] != -1:
                continue
            comp[u] = c
            for w in rgraph[u]:
                if comp[w] == -1:
                    stack.append(w)

    for v in reversed(order):
        if comp[v] == -1:
            dfs2(v, c_id[0])
            c_id[0] += 1

    return all(comp[2*i] != comp[2*i+1] for i in range(n))


# ── Instance generators ────────────────────────────────────────────────────────

def gen_2sat(n: int, m: int, seed: int) -> list:
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        a, b = rng.sample(range(1, n+1), 2)
        clauses.append((a * rng.choice([1,-1]), b * rng.choice([1,-1])))
    return clauses


def gen_3sat(n: int, m: int, seed: int) -> list:
    rng = random.Random(seed)
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n+1), 3)
        clauses.append(tuple(v * rng.choice([1,-1]) for v in vs))
    return clauses


# ── Wilson CI ─────────────────────────────────────────────────────────────────

def wilson_ci(k: int, n: int, z: float = 1.96) -> tuple:
    if n == 0:
        return 0.0, 0.0
    p = k / n
    center = (p + z**2/(2*n)) / (1 + z**2/n)
    margin = (z/(1+z**2/n)) * math.sqrt(p*(1-p)/n + z**2/(4*n**2))
    return max(0.0, center-margin), min(1.0, center+margin)


# ── Experiment ────────────────────────────────────────────────────────────────

CONFIG = {
    "2sat": {
        "n_values": [5, 8, 12],
        "ratios":   [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0],
        "trials":   100,
        "sat_threshold": 1.0,  # 2-SAT threshold is at ratio 1 (approx)
    },
    "3sat": {
        "n_values": [8, 12, 15],
        "ratios":   [2.5, 3.0, 3.5, 3.8, 4.0, 4.267, 4.5, 5.0, 6.0],
        "trials":   50,
        "sat_threshold": 4.267,
    },
}


def run_suite(suite: str):
    cfg = CONFIG[suite]
    gen = gen_2sat if suite == "2sat" else gen_3sat
    sat_fn = is_2sat if suite == "2sat" else None  # 3-SAT uses DPLL below

    print(f"{'='*72}")
    print(f"CLAUSE COVER NERVE H_1  --  {suite.upper()}")
    print(f"Hypothesis: H_1(nerve) != 0 iff UNSAT")
    print(f"{'='*72}")

    for n in cfg["n_values"]:
        print(f"\nn={n}  ({cfg['trials']} trials per ratio)")
        print(f"{'ratio':>7}  {'SAT frac':>10}  {'H1>0 frac':>10}  {'correct?':>10}")
        print("-" * 44)

        for ratio in cfg["ratios"]:
            m = round(ratio * n)
            T = cfg["trials"]
            sat_count = h1_nonzero_count = correct_count = 0

            for trial in range(T):
                seed = hash((suite, n, ratio, trial)) & 0xFFFFFF
                clauses = gen(n, m, seed)

                if suite == "2sat":
                    sat = is_2sat(n, clauses)
                else:
                    sat = _dpll_small([list(c) for c in clauses], {})

                h1 = compute_nerve_h1(n, clauses)
                h1_pos = h1 > 0

                if sat:
                    sat_count += 1
                if h1_pos:
                    h1_nonzero_count += 1

                # Hypothesis: H_1 != 0 iff UNSAT
                # So correct prediction: (h1_pos == (not sat))
                predicted_unsat = h1_pos
                if predicted_unsat == (not sat):
                    correct_count += 1

                with open(LOG_PATH, "a") as f:
                    f.write(json.dumps({
                        "suite": suite, "n": n, "m": m, "ratio": ratio,
                        "trial": trial, "sat": sat, "dim_h1": h1,
                        "h1_positive": h1_pos,
                        "correct_prediction": predicted_unsat == (not sat),
                        "timestamp": int(time.time()),
                    }) + "\n")

            sat_frac  = sat_count / T
            h1_frac   = h1_nonzero_count / T
            acc       = correct_count / T
            lo, hi    = wilson_ci(correct_count, T)
            marker    = "  <-- threshold" if abs(ratio - cfg["sat_threshold"]) < 0.05 else ""

            print(f"{ratio:>7.3f}  {sat_frac:>10.2f}  {h1_frac:>10.2f}  "
                  f"{acc:>8.2f} [{lo:.2f},{hi:.2f}]{marker}")


def assess(suite: str):
    """Read logged results and print per-n accuracy summary."""
    cfg = CONFIG[suite]
    results = {}

    with open(LOG_PATH) as f:
        for line in f:
            r = json.loads(line)
            if r["suite"] != suite:
                continue
            key = (r["n"], r["ratio"])
            if key not in results:
                results[key] = {"correct": 0, "total": 0, "sat": 0, "h1pos": 0}
            results[key]["total"]   += 1
            results[key]["correct"] += int(r["correct_prediction"])
            results[key]["sat"]     += int(r["sat"])
            results[key]["h1pos"]   += int(r["h1_positive"])

    # Per n: what fraction of (ratio, trial) pairs are correctly predicted?
    print(f"\n{'='*72}")
    print(f"VERDICT  --  {suite.upper()}")
    print(f"{'='*72}")
    for n in cfg["n_values"]:
        total_correct = sum(v["correct"] for (nn,_),v in results.items() if nn==n)
        total_all     = sum(v["total"]   for (nn,_),v in results.items() if nn==n)
        if total_all == 0:
            continue
        acc = total_correct / total_all
        lo, hi = wilson_ci(total_correct, total_all)
        print(f"  n={n:2d}  overall accuracy: {acc:.3f}  CI=[{lo:.3f},{hi:.3f}]")

    # Overall verdict
    all_correct = sum(v["correct"] for v in results.values())
    all_total   = sum(v["total"]   for v in results.values())
    if all_total == 0:
        print("  No data.")
        return
    acc = all_correct / all_total
    lo, hi = wilson_ci(all_correct, all_total)
    print(f"\n  OVERALL accuracy: {acc:.3f}  CI=[{lo:.3f},{hi:.3f}]")
    if lo > 0.90:
        print("  VERDICT: PROMISING -- hypothesis holds at >90% CI lower bound.")
        print("  Recommendation: increase n and trials, then pursue Lean formalization.")
    elif lo > 0.70:
        print("  VERDICT: WEAK -- hypothesis partially holds but not conclusive.")
        print("  Recommendation: investigate failure cases before committing to Lean.")
    else:
        print("  VERDICT: FAIL -- hypothesis does not hold reliably.")
        print("  Recommendation: investigate candidate (b) (relative cohomology).")


if __name__ == "__main__":
    suite = sys.argv[1] if len(sys.argv) > 1 else "2sat"
    if suite not in ("2sat", "3sat", "both"):
        print("Usage: python empirical_nerve_h1.py [2sat|3sat|both]")
        sys.exit(1)

    suites = ["2sat", "3sat"] if suite == "both" else [suite]
    for s in suites:
        t0 = time.time()
        run_suite(s)
        assess(s)
        print(f"\n[{s} done in {time.time()-t0:.1f}s]")

    print(f"\nResults logged to: {LOG_PATH}")
