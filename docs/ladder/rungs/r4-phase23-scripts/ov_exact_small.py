"""EXACT first round for the all-pairs family on n <= 7 vertices: q = sum of edge indicators of a graph H on n vertices,
every graph up to isomorphism (networkx atlas, 1253 graphs on <= 7 nodes); the rank depends only on the isomorphism class of H
(variables are exchangeable).  usage: ov_exact_small.py n K"""
import sys, networkx as nx
from networkx.generators.atlas import graph_atlas_g
from ov_lib import *
n, K = int(sys.argv[1]), int(sys.argv[2])
sets = pair_sets(n); F = Fam(n, sets, K); idx = {(i, j): t for t, (i, j) in enumerate(itertools.combinations(range(n), 2))}
c0 = F.rank_of([]); best = (c0, None); res = []
for H in graph_atlas_g():
    if H.number_of_nodes() != n or H.number_of_edges() == 0: continue
    c = np.zeros(F.s, dtype=np.int64)
    for u, v in H.edges(): c[idx[(min(u, v), max(u, v))]] = 1
    r = F.rank_of([c]); res.append((r, H.number_of_edges()))
    if r < best[0]: best = (r, sorted(H.edges()))
print(f"n={n} K={K} s={F.s} c0={c0} theta1={F.theta1():.4f} pang={F.pang():.4f}  EXACT best c1={best[0]} gain={1-best[0]/c0:.4f} ratio_to_theta1={(1-best[0]/c0)/F.theta1():.3f} edges={best[1]}")
