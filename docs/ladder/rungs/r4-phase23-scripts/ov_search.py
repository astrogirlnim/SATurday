"""Overlapping-family search (SAMPLED upper bound on c_t, i.e. LOWER bound on the best gain).  usage:
  ov_search.py family n rho K T [seed]      family in {all, rand<s>, cycle, cubic, rg<s>, rt<s>, sts}   (all = every rho-subset of n variables)
Round 1 seeds: (a) single term, (b) clique-type q = all rho-subsets inside the first m variables, m = rho..n,
(c) random sets of terms of several densities.  Then single-term flip hill climbing.  Rounds 2..T: greedy (best c_t given
previous c_1..c_{t-1}) with the same seeds + flips.  Also prints theta1 and Pang eta."""
import sys, itertools, random
from ov_lib import *
fam, n, rho, K, T = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
seed = int(sys.argv[6]) if len(sys.argv) > 6 else 1
rnd = random.Random(seed)
if fam == 'all': sets = pair_sets(n) if rho == 2 else triple_sets(n)
elif fam.startswith('rand'): sets = random_sets(n, rho, int(fam[4:]), seed)
else: sets = sparse_sets(fam, n, seed)
F = Fam(n, sets, K); s = F.s
c0 = F.rank_of([]); th = F.theta1()
print(f"family={fam} n={n} rho={rho} K={K} s={s} c0={c0} theta1={th:.5f} pang={F.pang():.5f}", flush=True)
def clique(m):
    mask = (1 << m) - 1
    return np.array([1 if (S & ~mask) == 0 else 0 for S in F.sets], dtype=np.int64)
def hill(prev, c, rounds=3):
    cur = F.rank_of(prev + [c])
    for _ in range(rounds):
        improved = False
        for j in rnd.sample(range(s), min(s, 150)):
            c[j] ^= 1
            if c.any():
                r = F.rank_of(prev + [c])
                if r < cur: cur = r; improved = True
                else: c[j] ^= 1
            else: c[j] ^= 1
        if not improved: break
    return cur, c
prev = []; cur0 = c0
for t in range(1, T + 1):
    cands = []
    for j in rnd.sample(range(s), min(s, 3)):
        c = np.zeros(s, dtype=np.int64); c[j] = 1; cands.append(('single', c))
    for m in range(rho, n + 1):
        if clique(m).any(): cands.append((f'clique{m}', clique(m)))
    for dens in (0.5, 0.25, 0.1, 0.03):
        for _ in range(3): cands.append((f'rand{dens}', (np.random.RandomState(rnd.randrange(10**6)).rand(s) < dens).astype(np.int64)))
    scored = sorted(((F.rank_of(prev + [c]), nm, c) for nm, c in cands if c.any()), key=lambda x: x[0])
    best = None
    for r, nm, c in scored[:4]:
        r2, c2 = hill(prev, c.copy())
        if best is None or r2 < best[0]: best = (r2, nm, c2.copy(), r)
    prev.append(best[2])
    g_round = 1 - best[0] / cur0
    print(f"  t={t}: c_t={best[0]} (seed {best[1]} -> {best[3]}, after hill {best[0]}) round gain={g_round:.4f} ratio_to_theta1={g_round/th if th else float('nan'):.2f}  cum rate={1-(best[0]/c0)**(1/t):.4f} |c|={int(best[2].sum())}", flush=True)
    cur0 = best[0]
    if best[0] == 0: break
