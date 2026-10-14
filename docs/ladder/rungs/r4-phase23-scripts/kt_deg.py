"""Structured instances with PC degree above width, over F_p.  usage: kt_deg.py name p
names: php3 (4 pigeons, 3 holes, 12 vars), php2 (3 pigeons, 2 holes), tsK5 (Tseitin mod 2, K5, 10 vars),
tsK5q3 (Tseitin mod 3 with Boolean edge variables, K5), tsK6 (Tseitin mod 2, K6, 15 vars)."""
import sys, time, itertools
from pcdeg import *
from cnfs import *

def php(P, H, p):
    var = lambda i, j: i * H + j; ax = []
    for i in range(P): ax.append(forbid_poly([var(i, j) for j in range(H)], [0] * H, p))
    for j in range(H):
        for i, k in itertools.combinations(range(P), 2): ax.append(forbid_poly([var(i, j), var(k, j)], [1, 1], p))
    return P * H, ax

def instance(name, p):
    if name == 'php3': return php(4, 3, p)
    if name == 'php2': return php(3, 2, p)
    if name == 'tsK5': return tseitin_mod2(complete(5), 5, [1, 0, 0, 0, 0], p)
    if name == 'tsK5q3': return tseitin_modq(complete(5), 5, [1, 0, 0, 0, 0], 3, p)
    if name == 'tsK6': return tseitin_mod2(complete(6), 6, [1, 1, 0, 0, 0, 0], p)

if __name__ == '__main__':
    name, p = sys.argv[1], int(sys.argv[2]); n, ax = instance(name, p); t = time.time()
    print(name, 'p', p, 'n', n, 'PC degree', pc_degree(n, ax, p), f'{time.time()-t:.0f}s', flush=True)
