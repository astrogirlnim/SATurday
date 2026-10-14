"""EXACT first round for a sparse overlapping family with s <= 16 terms: all 2^s - 1 nonzero c are tried (no sampling).
usage: ov_exact_sparse.py family n rho K [seed]"""
import sys
from ov_lib import *
fam, n, rho, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
sets = sparse_sets(fam, n, seed); F = Fam(n, sets, K); s = F.s; assert s <= 16
c0 = F.rank_of([]); best = (c0, 0)
Gi = F.G.astype(np.int64)
for m in range(1, 1 << s):
    c = np.array([(m >> j) & 1 for j in range(s)], dtype=np.int64)
    r = F.rank_of([c])
    if r < best[0]: best = (r, m)
    if len(F.cache) > 20000: F.cache.clear()
g = 1 - best[0] / c0
print(f"EXACT round1 {fam} n={n} rho={rho} K={K} s={s} c0={c0} theta1={F.theta1():.5f} best c1={best[0]} gain={g:.4f} ratio={g/F.theta1():.2f} |c|={bin(best[1]).count('1')} terms={[bin(sets[j]).count('1') and [i for i in range(n) if sets[j]>>i&1] for j in range(s) if best[1]>>j&1]}", flush=True)
