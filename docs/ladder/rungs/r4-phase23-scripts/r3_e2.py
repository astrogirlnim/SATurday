import sys, random, math, numpy as np
from r3lib import *
def rand_subcube(cube, rho, rnd, blocks=None):
    n = cube.n
    vs = rnd.sample(range(n), rho) if blocks is None else blocks
    fs = []
    for v in vs:
        a = [0] * n; a[v] = 1
        fs.append((a, rnd.choice([0, cube.p - 1])))   # x_v = 0  or  x_v - 1 = 0
    return fs
def rand_affine(cube, rho, rnd, wt):
    n, p = cube.n, cube.p
    while True:
        fs = []
        for _ in range(rho):
            a = [0] * n
            for i in rnd.sample(range(n), wt): a[i] = rnd.randint(1, p - 1)
            fs.append((a, rnd.randint(0, p - 1)))
        g = cube.indicator(fs)
        if g.sum() > 0: return fs
def greedy(cube, Q, K, gs, rnd, ncomb=40, maxr=40):
    p = cube.p; s = len(gs)
    P = np.ones(cube.N, dtype=np.int64)
    c = [stack_rank(cube, Q, K, P, gs)]
    combos = span_combos(s, p)
    while c[-1] > 0 and len(c) <= maxr:
        cs = combos if len(combos) <= ncomb else rnd.sample(combos, ncomb)
        best = None
        for co in cs:
            P2 = P * Pprime(cube, gs, co)
            r = stack_rank(cube, Q, K, P2, gs)
            if best is None or r < best[0]: best = (r, P2)
        c.append(best[0]); P = best[1]
        if c[-1] == c[-2] and len(c) > 3 and c[-1] == c[-3]: break
    return c
def exp(n, p, K, rho, s, kind, seed=0, wt=3):
    cube = Cube(n, p); rnd = random.Random(seed); Q = Quot(cube, None)
    gs = []
    for i in range(s):
        if kind == 'subcube': fs = rand_subcube(cube, rho, rnd)
        elif kind == 'blocks': fs = rand_subcube(cube, rho, rnd, blocks=list(range(i * rho % n, i * rho % n + rho)) if (i+1)*rho<=n else None)
        else: fs = rand_affine(cube, rho, rnd, wt)
        gs.append(cube.indicator(fs))
    c = greedy(cube, Q, K, gs, rnd)
    d = (p - 1) * rho
    etaP = (1 - 1 / p) * cube.NK(max(K - d, 0)) / cube.NK(K) if K >= d else float('nan')
    t = len(c) - 1
    eta1 = 1 - c[1] / c[0] if t >= 1 and c[0] else float('nan')
    print(f"n={n} p={p} K={K} rho={rho} s={s} {kind}: c={c} first-round reduction={eta1:.3f} PangEta={etaP:.4f} (K/n)^rho={(K/n)**rho:.4f}")
if __name__ == '__main__':
    n = int(sys.argv[1]); p = int(sys.argv[2])
    for rho in (1, 2, 3):
        for K in (2, 3):
            for kind in ('subcube', 'affine'):
                if p == 2 and kind == 'affine': continue
                for s in (4, 8):
                    exp(n, p, K, rho, s, kind, seed=rho * 10 + K)
