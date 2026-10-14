"""Kill test (r4-phase23-killtest.md): EXACT multi-round optimum of Pang-style q-sequences, p=2, C_D=0,
block family g_i = [x_{B_i}=0], B_i disjoint blocks of size rho, s=n//rho blocks.

Reduction (proved in the note): a point x has pattern a(x) in F_2^s (a_i = g_i(x)).  After rounds with
q_k = c_k . g, P = prod [q_k=0] keeps exactly the points with a(x) in A\{0}, A = span(c_k)^perp, a subspace of
codim <= t.  So c_t(K) = rank of V_K restricted to U_A = {x : a(x) in A\{0}}, and the exact optimum over ALL
t-round q-sequences (adaptive or not) is min over subspaces A of F_2^s of codim t.  Rank depends only on A up to
coordinate permutation (blocks are exchangeable), so we enumerate orbit representatives.
usage: python3 kt_opt.py n rho K [K...]"""
import sys, itertools, math
import numpy as np

def canon_tables(s):
    perms = list(itertools.permutations(range(s)))
    vec = np.arange(1 << s)
    tab = np.zeros((len(perms), 1 << s), dtype=np.int32)       # tab[k][v] = image of v under perm k
    for k, pm in enumerate(perms):
        img = np.zeros(1 << s, dtype=np.int32)
        for i in range(s): img |= ((vec >> i) & 1) << pm[i]
        tab[k] = img
    return tab

def span_mask(gens, s):
    vs = {0}
    for g in gens: vs |= {v ^ g for v in vs}
    m = np.zeros(1 << s, dtype=bool); m[list(vs)] = True
    return m

def canon(mask, tab):
    # image sets of the subspace under all perms; canonical = lexicographically smallest packed bitset
    imgs = np.zeros_like(tab, dtype=bool)
    idx = np.nonzero(mask)[0]
    rows = np.arange(tab.shape[0])[:, None]
    imgs[rows, tab[:, idx]] = True
    packed = np.packbits(imgs, axis=1)
    best = min(range(packed.shape[0]), key=lambda k: packed[k].tobytes()) if packed.shape[0] < 2000 else None
    if best is None:
        order = np.lexsort(packed.T[::-1]); best = order[0]
    return packed[best].tobytes(), imgs[best]

def subspace_orbits(s):
    """orbit representatives of all subspaces of F_2^s by dimension: reps[k] = list of boolean masks"""
    tab = canon_tables(s)
    reps = {0: {canon(span_mask([], s), tab)[0]: span_mask([], s)}}
    for k in range(s):
        nxt = {}
        for m in reps[k].values():
            gens_vs = np.nonzero(m)[0]
            for v in range(1, 1 << s):
                if m[v]: continue
                m2 = m | m[np.arange(1 << s) ^ v]               # span(A, v) = A union (A + v)
                key, cm = canon(m2, tab)
                if key not in nxt: nxt[key] = cm
        reps[k + 1] = nxt
    return {k: list(v.values()) for k, v in reps.items()}

def sampled_subspaces(s, nsamp, seed=1):
    """for each dim k: coordinate subspace span(e_0..e_{k-1}) (= sequential q=g_i rounds) + random subspaces"""
    import random
    rnd = random.Random(seed); reps = {}
    for k in range(s + 1):
        L = [span_mask([1 << i for i in range(k)], s)]
        for _ in range(0 if k in (0, s) else nsamp):
            gens, m = [], span_mask([], s)
            while len(gens) < k:                                  # exactly dim k (independent generators)
                v = rnd.randrange(1, 1 << s)
                if not m[v]: gens.append(v); m = span_mask(gens, s)
            L.append(m)
        reps[k] = L
    return reps

def gf2_rank(rows):
    basis = {}
    r = 0
    for x in rows:
        while x:
            h = x.bit_length() - 1
            if h in basis: x ^= basis[h]
            else: basis[h] = x; r += 1; break
    return r

def main():
    n, rho = int(sys.argv[1]), int(sys.argv[2]); Ks = [int(k) for k in sys.argv[3:]]
    s = n // rho
    N = 1 << n; pts = np.arange(N)
    pat = np.zeros(N, dtype=np.int32)                               # pattern of each point
    for i in range(s):
        blk = ((1 << rho) - 1) << (i * rho)
        pat |= (((pts & blk) == 0).astype(np.int32)) << i
    exact = s <= 7                     # orbit enumeration over S_s is only feasible for s <= 7
    if exact:
        reps = subspace_orbits(s)
        print(f"n={n} rho={rho} s={s}: EXACT; subspace orbits by dim: " + str({k: len(v) for k, v in reps.items()}), flush=True)
    else:
        reps = sampled_subspaces(s, int(__import__('os').environ.get('NSAMP', '40')))
        print(f"n={n} rho={rho} s={s}: SAMPLED (min over random + coordinate subspaces = upper bound on the optimum)", flush=True)
    for K in Ks:
        ms = [m for m in range(N) if bin(m).count('1') <= K]
        vals = np.array([(pts & m) == m for m in ms])                # N(K) x 2^n bool
        def crank(mask):
            keep = mask[pat] & (pat != 0)
            sub = np.packbits(vals[:, keep], axis=1)
            return gf2_rank([int.from_bytes(r.tobytes(), 'big') for r in sub])
        NK = lambda m, k: sum(math.comb(m, j) for j in range(k + 1))
        c0 = crank(reps[s][0])                                       # A = whole space (t=0)
        th1 = NK(n - rho, K - rho) / NK(n, K) if K >= rho else 0.0
        pang = 0.5 * NK(n, K - rho) / NK(n, K) if K >= rho else 0.0
        print(f"\n K={K}: c0={c0}  theta1=N_{{n-rho}}(K-rho)/N_n(K)={th1:.5f}  Pang eta={pang:.5f}  (K/n)^rho={(K/n)**rho:.5f}")
        print("   t  best c_t   c_t/c_0   rate=1-(c_t/c_0)^(1/t)   (1-theta1)^t   (1-eta)^t   n_orbits")
        for t in range(0, s + 1):
            cand = reps[s - t]
            best = min(crank(m) for m in cand)
            rt = (1 - (best / c0) ** (1 / t)) if (t and best > 0) else float('nan')
            print(f"  {t:2d} {best:8d}  {best/c0:9.5f}   {rt:9.5f}   {(1-th1)**t:9.5f}  {(1-pang)**t:9.5f}   {len(cand)}", flush=True)

main()
