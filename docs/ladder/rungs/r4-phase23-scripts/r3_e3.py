import sys, random, time, numpy as np
import pcdeg
from pcdeg import *
from cnfs import rand3cnf
from r3lib import *
from r3_e2 import greedy, rand_subcube
def closureS(n, axioms, D, p):
    """copy of pc_closure_has_one that returns (has_one, S, sp)"""
    sp = Space(n, D)
    A = np.array([poly_vec(sp, a, p) for a in axioms]); S, piv = rref(A, p); top = sp.deg == D
    while True:
        if has_one(S, sp): return True, S, sp
        lead = np.array([sp.deg[c] for c in piv]); new = []
        low = S[lead < D]; hi = S[lead == D]
        for i in range(n):
            if low.shape[0]: new.append(sp.mulrows(low, i, p))
            if hi.shape[0]:
                cols = [c for c in np.nonzero(top)[0] if not (sp.masks[c] >> i) & 1]
                if not cols: comb = hi
                else:
                    Am = hi[:, cols]; t = hi.shape[0]
                    aug = np.concatenate([Am, np.eye(t, dtype=np.int64)], axis=1)
                    R, pv = rref(aug, p)
                    ker = R[[k for k in range(R.shape[0]) if not R[k, :len(cols)].any()]][:, len(cols):]
                    if ker.shape[0] == 0: continue
                    comb = (ker @ hi) % p
                new.append(sp.mulrows(comb, i, p))
        if not new: return False, S, sp
        S2, piv2 = rref(np.concatenate([S] + new), p)
        if S2.shape[0] == S.shape[0]: return False, S, sp
        S, piv = S2, piv2
def CD_function_rows(cube, S, sp):
    """rows of C_D as value vectors on the cube"""
    rows = []
    for r in S:
        c = np.zeros(cube.N, dtype=np.int64)
        for j in np.nonzero(r)[0]: c[sp.masks[j]] = r[j]
        rows.append(cube.to_val(c))
    return np.array(rows)
if __name__ == '__main__':
    p = int(sys.argv[1]); n = int(sys.argv[2]); m0 = int(sys.argv[3])
    for seed in range(40):
        nn, ax = rand3cnf(n, m0, p, seed)
        D = None
        t = time.time()
        for DD in range(3, n + 1):
            h, S, sp = closureS(nn, ax, DD, p)
            if h: D = DD; break
            Slast = (S, sp, DD)
        if D is None: continue
        if D < 5: continue
        S, sp, DD = Slast
        cube = Cube(n, p); rows = CD_function_rows(cube, S, sp)
        Q0 = Quot(cube, None); Q = Quot(cube, rows)
        print(f"seed={seed} n={n} p={p} m={m0} PCdeg={D}; use D={DD}, dim C_D={Q.dim}, time {time.time()-t:.0f}s", flush=True)
        rnd = random.Random(seed)
        for rho in (1, 2):
            d = (p - 1) * rho
            for K in range(d, DD - d + 1):
                for s in (4, 8):
                    gs = [cube.indicator(rand_subcube(cube, rho, rnd)) for _ in range(s)]
                    rr = random.Random(1)
                    c0 = greedy(cube, Q0, K, gs, rr, ncomb=20, maxr=3)
                    cC = greedy(cube, Q, K, gs, random.Random(1), ncomb=20, maxr=3)
                    print(f"  rho={rho} K={K} s={s}: noC c={c0}   withC c={cC}", flush=True)
        break
