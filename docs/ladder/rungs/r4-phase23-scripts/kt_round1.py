"""First-round exact optimum for the block family, p=2, C_D=0: q = sum_{i in W} g_i, |W| = w (rank of V_K on points whose
pattern a has a != 0 and |a & W| even).  usage: kt_round1.py n rho K [K...]  -> gain per weight w, vs theta1"""
import sys, math, numpy as np
n, rho = int(sys.argv[1]), int(sys.argv[2]); s = n // rho; N = 1 << n; pts = np.arange(N)
pat = np.zeros(N, dtype=np.int32)
for i in range(s): pat |= (((pts & (((1 << rho) - 1) << (i * rho))) == 0).astype(np.int32)) << i
pc = np.array([bin(v).count('1') for v in range(1 << s)])
def gf2_rank(rows):
    basis = {}; r = 0
    for x in rows:
        while x:
            h = x.bit_length() - 1
            if h in basis: x ^= basis[h]
            else: basis[h] = x; r += 1; break
    return r
NK = lambda m, k: sum(math.comb(m, j) for j in range(k + 1))
for K in map(int, sys.argv[3:]):
    ms = [m for m in range(N) if bin(m).count('1') <= K]; vals = np.array([(pts & m) == m for m in ms])
    def crank(keep): return gf2_rank([int.from_bytes(r.tobytes(), 'big') for r in np.packbits(vals[:, keep], axis=1)])
    c0 = crank(pat != 0); th = NK(n - rho, K - rho) / NK(n, K) if K >= rho else 0
    out = []
    for w in range(1, s + 1):
        W = (1 << w) - 1; keep = (pat != 0) & (pc[pat & W] % 2 == 0)
        out.append(f"w={w}: {1 - crank(keep) / c0:.4f}")
    print(f"n={n} rho={rho} K={K} c0={c0} theta1={th:.4f}  " + "  ".join(out), flush=True)
