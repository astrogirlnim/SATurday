"""Upper-bound-first probe (p odd, Tseitin mod 2 with Boolean edge variables).  Uses chain_ub.py (PC-degree upper bound from a vertex
ordering, r4-phase23-program.md Sec 2.5).  A PC degree D gives a depth-1 algebraic (PC over F_p) refutation of size <= N(D) = sum_{j<=D} C(E,j).
Prints D_ub, log2 of that size bound, and the log2 size bound divided by E, for ladders (cutwidth O(1)) and random cubic graphs (expanders)."""
import math, random, networkx as nx
from chain_ub import best_order
def logN(E, D): return math.log2(sum(math.comb(E, j) for j in range(D+1)))
rng = random.Random(1)
print('graph        V    E   D_ub  log2N(E,D_ub)  log2N/E')
for m in (4, 8, 16, 32, 64):
    G = nx.ladder_graph(m); E = G.number_of_edges(); D = best_order(G, 6, rng)
    print(f'ladder{m:<6} {G.number_of_nodes():4d} {E:4d} {D:5d} {logN(E,D):10.1f} {logN(E,D)/E:9.3f}')
for V in (10, 20, 40, 80, 160):
    G = nx.random_regular_graph(3, V, seed=5); E = G.number_of_edges(); D = best_order(G, 6, rng)
    print(f'cubic{V:<7} {V:4d} {E:4d} {D:5d} {logN(E,D):10.1f} {logN(E,D)/E:9.3f}')
