import sys, random, math, numpy as np
from r3lib import *
def supp_dim(cube, K, g):
    """dim {f in V_K : f vanishes off supp g}"""
    B = cube.Vbasis(K); off = np.nonzero(g == 0)[0]
    return B.shape[0] - rank_mod(B[:, off], cube.p)
def forms_subcube(n, rho): 
    return [([1 if j == i else 0 for j in range(n)], 0) for i in range(rho)]
def forms_dense(n, rho, rnd, p, wt=None):
    fs = []
    for _ in range(rho):
        while True:
            S = range(n) if wt is None else rnd.sample(range(n), wt)
            a = [0] * n
            for i in S: a[i] = rnd.randint(1, p - 1)
            a0 = rnd.randint(0, p - 1)
            fs.append((a, a0)); break
    return fs
def run(n, p, K, kinds, rhos, seed=1):
    cube = Cube(n, p); rnd = random.Random(seed); NK = cube.NK(K)
    for kind in kinds:
        row = []
        for rho in rhos:
            if kind == 'subcube': fs = forms_subcube(n, rho)
            elif kind == 'dense': fs = forms_dense(n, rho, rnd, p)
            elif kind == 'wt3': fs = forms_dense(n, rho, rnd, p, 3)
            g = cube.indicator(fs)
            z = supp_dim(cube, K, g)
            d = (p - 1) * rho
            row.append((rho, int(g.sum()), z, z / NK, (K / (n - K)) ** rho if K < n else 0, (1 - 1 / p) * cube.NK(max(K - d, 0)) / NK))
        print(f"n={n} p={p} K={K} {kind}: " + "; ".join(f"rho={r}: |T|={t} z={z} z/N={zn:.4f} (K/(n-K))^rho={a:.4f} PangN(K-d)/N(K)={b:.4f}" for r, t, z, zn, a, b in row))
if __name__ == '__main__':
    for p in (2, 3):
        for K in (2, 3, 4):
            run(10, p, K, ['subcube', 'dense', 'wt3'], [1, 2, 3])
