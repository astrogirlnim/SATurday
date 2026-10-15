"""Block-aligned (multiplication-closed) subspace test.  p=2.  Follows r4-phase23-overlap.md Sec 5 item 4.
W_{k,t}(F) = span{ [x_m=1] * [x_U=0] : |m|<=k, U = union of at most t sets of the family F, m disjoint from U }
(functions on {0,1}^n over GF(2)).  W_{k,0}=V_k.  W_{k,t} is the part of the smallest subspace containing V_k and closed
under multiplication by the g_S=[x_S=0] that is reachable with t multiplications.
Reports dim W_{k,t}, the Hilbert ratio dim W_{K-rho,t}/dim W_{K,t} and compares it with
N(K-rho)/N(K) (the V_K ratio) and with K/n (the hoped-for ratio).
usage: python3 blockalign.py n rho K tmax [disjoint|cycle|cubic|random S]"""
import sys, itertools, math, random
sys.path.insert(0, __import__('os').path.dirname(__file__))
from ov_lib import gf2_rank, NK

def table(n, ones_mask, zeros_mask):
    # truth table of [x_ones=1][x_zeros=0] as int bitmask over points 0..2^n-1
    N = 1 << n; t = 0
    for x in range(N):
        if (x & ones_mask) == ones_mask and (x & zeros_mask) == 0: t |= 1 << x
    return t

def fam(kind, n, rho, S=0, seed=1):
    if kind == 'disjoint': return [sum(1 << (b*rho+i) for i in range(rho)) for b in range(n // rho)]
    if kind == 'cycle': return [sum(1 << ((j+i) % n) for i in range(rho)) for j in range(n)]
    if kind == 'random':
        r = random.Random(seed); out = set()
        while len(out) < S: out.add(sum(1 << i for i in r.sample(range(n), rho)))
        return sorted(out)
    raise SystemExit('kind')

def dimW(n, F, k, t):
    Us = {0}
    for r in range(1, t+1):
        for c in itertools.combinations(F, r):
            u = 0
            for s in c: u |= s
            Us.add(u)
    rows = set()
    N = 1 << n
    for u in Us:
        free = [i for i in range(n) if not (u >> i) & 1]
        for j in range(k+1):
            for m in itertools.combinations(free, j):
                mm = sum(1 << i for i in m)
                rows.add(table(n, mm, u))
    return gf2_rank(list(rows))

if __name__ == '__main__':
    n, rho, K, tmax = map(int, sys.argv[1:5]); kind = sys.argv[5] if len(sys.argv) > 5 else 'disjoint'
    S = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    F = fam(kind, n, rho, S)
    print(f'n={n} rho={rho} K={K} family={kind} s={len(F)}  2^n={1<<n}')
    print(f'V ratio N(K-rho)/N(K) = {NK(n,K-rho)/NK(n,K):.4g}   K/n = {K/n:.3g}   (K/n)^rho = {(K/n)**rho:.3g}')
    for t in range(0, tmax+1):
        a = dimW(n, F, K, t); b = dimW(n, F, K-rho, t) if K-rho >= 0 else 0
        print(f't={t}: dim W_K={a}  dim W_(K-rho)={b}  ratio={b/a:.4g}  (dim V_K={NK(n,K)})  N(K+t*rho)={NK(n,K+t*rho)}  dimW_K/N(K+t*rho)={a/NK(n,K+t*rho):.3f}', flush=True)
