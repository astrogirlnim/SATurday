"""
CNF family generators for the proof complexity ladder falsifier.

Families (all deterministic, all with exact pre-generation cost estimation):

1. php(n): pigeonhole PHP(n+1, n). Unsatisfiable for every n >= 1. The R1 target
   family: resolution refutations require exponential size (Haken 1985).
2. tseitin(n): odd-charge Tseitin contradiction over a fixed 3-regular circulant
   graph on n vertices (n even). Unsatisfiable by the parity argument (total
   charge is odd). Hard for resolution over expanders (Urquhart; R2 family).
3. random_kcnf(n, density, k, seed): seeded random k-CNF. Above the satisfiability
   threshold (density 4.267 for k=3) instances are unsatisfiable with high
   probability and require exponential resolution refutations (Chvatal-Szemeredi).

Every generator returns (num_vars, clauses) with clauses as a list of tuples of
nonzero ints in DIMACS convention. Estimators compute exact variable and clause
counts plus a byte estimate WITHOUT generating the formula, so the budget check
runs first (docs/p-vs-np-stop-conditions.md).

LOG: proof complexity family generators module
"""

import random
import sys
from pathlib import Path
from typing import Dict, List, Tuple

Clause = Tuple[int, ...]


def log(message: str) -> None:
    """Log to stderr with a stable prefix so runner output stays parseable."""
    print(f"[families] {message}", file=sys.stderr)


# ------------------------------------------------------------------ PHP -----


def php_var(pigeon: int, hole: int, n_holes: int) -> int:
    """DIMACS variable for 'pigeon sits in hole' (both one-indexed)."""
    return (pigeon - 1) * n_holes + hole


def php_estimate(n: int) -> Dict[str, int]:
    """Exact size estimate for PHP(n+1, n) without generating it."""
    pigeons = n + 1
    num_vars = pigeons * n
    pigeon_clauses = pigeons                       # each pigeon in some hole
    hole_clauses = n * (pigeons * (pigeons - 1)) // 2  # no two pigeons share a hole
    num_clauses = pigeon_clauses + hole_clauses
    # Byte estimate: literals are at most len(str(num_vars)) + 1 chars plus space.
    lit_width = len(str(num_vars)) + 2
    est_bytes = pigeon_clauses * (n * lit_width + 2) + hole_clauses * (2 * lit_width + 2) + 64
    return {
        "num_vars": num_vars,
        "num_clauses": num_clauses,
        "est_bytes": est_bytes,
    }


def php_cnf(n: int) -> Tuple[int, List[Clause]]:
    """
    PHP(n+1, n): n+1 pigeons, n holes.

    Clauses:
    - For each pigeon i: (p_i1 or ... or p_in)   [pigeon must sit somewhere]
    - For each hole j and pigeons i < i': (not p_ij or not p_i'j)  [no sharing]

    Unsatisfiable by the pigeonhole principle. Non-vacuity: refutations exist by
    resolution completeness (R0), so lower bounds quantify over a nonempty set.
    """
    log(f"generating PHP({n + 1}, {n})")
    pigeons = n + 1
    num_vars = pigeons * n
    clauses: List[Clause] = []

    for i in range(1, pigeons + 1):
        clauses.append(tuple(php_var(i, j, n) for j in range(1, n + 1)))

    for j in range(1, n + 1):
        for i in range(1, pigeons + 1):
            for i2 in range(i + 1, pigeons + 1):
                clauses.append((-php_var(i, j, n), -php_var(i2, j, n)))

    log(f"PHP({n + 1}, {n}): {num_vars} vars, {len(clauses)} clauses")
    return num_vars, clauses


# -------------------------------------------------------------- Tseitin -----


def tseitin_edges(n: int) -> List[Tuple[int, int]]:
    """
    Fixed 3-regular circulant graph on n vertices (n even, n >= 4):
    cycle edges (v, v+1 mod n) plus chord edges (v, v + n/2) for v < n/2.
    Connected and 3-regular; chords give expander-like behavior for calibration.
    """
    edges = [(v, (v + 1) % n) for v in range(n)]
    edges += [(v, v + n // 2) for v in range(n // 2)]
    return edges


def tseitin_estimate(n: int) -> Dict[str, int]:
    """Exact size estimate for the odd-charge Tseitin formula on n vertices."""
    num_edges = n + n // 2
    num_clauses = 4 * n  # each degree-3 vertex contributes 4 parity clauses
    lit_width = len(str(num_edges)) + 2
    est_bytes = num_clauses * (3 * lit_width + 2) + 64
    return {
        "num_vars": num_edges,
        "num_clauses": num_clauses,
        "est_bytes": est_bytes,
    }


def tseitin_cnf(n: int) -> Tuple[int, List[Clause]]:
    """
    Odd-charge Tseitin contradiction on the fixed 3-regular circulant graph.

    Edge variables x_e. Vertex 0 has charge 1, all others charge 0; the sum of
    charges is odd, so the XOR system is unsatisfiable. Each vertex constraint
    XOR(e1, e2, e3) = charge becomes the 4 clauses over its incident edges whose
    sign patterns have the wrong parity.
    """
    if n % 2 != 0 or n < 4:
        raise ValueError(f"tseitin requires even n >= 4, got {n}")
    log(f"generating Tseitin odd-charge formula on {n} vertices")

    edges = tseitin_edges(n)
    edge_var = {frozenset(e): idx + 1 for idx, e in enumerate(edges)}
    incident: Dict[int, List[int]] = {v: [] for v in range(n)}
    for e in edges:
        var = edge_var[frozenset(e)]
        incident[e[0]].append(var)
        incident[e[1]].append(var)

    clauses: List[Clause] = []
    for v in range(n):
        evars = incident[v]
        assert len(evars) == 3, f"vertex {v} degree {len(evars)}, expected 3"
        charge = 1 if v == 0 else 0
        # XOR(a, b, c) = charge fails exactly on assignments with parity != charge.
        # Forbid each failing assignment with one clause.
        for a_sign in (0, 1):
            for b_sign in (0, 1):
                for c_sign in (0, 1):
                    if (a_sign + b_sign + c_sign) % 2 != charge:
                        clauses.append((
                            -evars[0] if a_sign else evars[0],
                            -evars[1] if b_sign else evars[1],
                            -evars[2] if c_sign else evars[2],
                        ))

    log(f"Tseitin({n}): {len(edges)} edge vars, {len(clauses)} clauses")
    return len(edges), clauses


# ---------------------------------------------------------- random k-CNF ----


def random_kcnf_estimate(n: int, density: float, k: int) -> Dict[str, int]:
    """Exact size estimate for random k-CNF with m = round(density * n) clauses."""
    m = round(density * n)
    lit_width = len(str(n)) + 2
    est_bytes = m * (k * lit_width + 2) + 64
    return {"num_vars": n, "num_clauses": m, "est_bytes": est_bytes}


def random_kcnf(n: int, density: float, k: int, seed: int) -> Tuple[int, List[Clause]]:
    """
    Seeded random k-CNF: m = round(density * n) clauses, each with k distinct
    variables and independent random signs. Deterministic for a fixed seed.

    At k = 3 and density 5.0 (above the 4.267 threshold) instances are
    unsatisfiable with high probability and hard for resolution.
    """
    log(f"generating random {k}-CNF: n={n}, density={density}, seed={seed}")
    rng = random.Random(seed)
    m = round(density * n)
    clauses: List[Clause] = []
    for _ in range(m):
        variables = rng.sample(range(1, n + 1), k)
        clauses.append(tuple(v if rng.random() < 0.5 else -v for v in variables))
    log(f"random {k}-CNF: {n} vars, {m} clauses")
    return n, clauses


# ------------------------------------------------------------- DIMACS IO ----


def write_dimacs(path: Path, num_vars: int, clauses: List[Clause], comment: str) -> int:
    """Write a DIMACS CNF file; returns bytes written. Streams clause by clause."""
    log(f"writing DIMACS to {path}")
    with open(path, "w") as f:
        f.write(f"c {comment}\n")
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(str(lit) for lit in clause) + " 0\n")
    size = path.stat().st_size
    log(f"wrote {size} bytes ({num_vars} vars, {len(clauses)} clauses)")
    return size


FAMILY_NAMES = ("php", "tseitin", "random-kcnf")


def estimate(family: str, n: int, density: float = 5.0, k: int = 3) -> Dict[str, int]:
    """Dispatch exact cost estimation for a family instance."""
    if family == "php":
        return php_estimate(n)
    if family == "tseitin":
        return tseitin_estimate(n)
    if family == "random-kcnf":
        return random_kcnf_estimate(n, density, k)
    raise ValueError(f"unknown family {family}; choose from {FAMILY_NAMES}")


def generate(
    family: str, n: int, density: float = 5.0, k: int = 3, seed: int = 42
) -> Tuple[int, List[Clause]]:
    """Dispatch generation for a family instance."""
    if family == "php":
        return php_cnf(n)
    if family == "tseitin":
        return tseitin_cnf(n)
    if family == "random-kcnf":
        return random_kcnf(n, density, k, seed)
    raise ValueError(f"unknown family {family}; choose from {FAMILY_NAMES}")
