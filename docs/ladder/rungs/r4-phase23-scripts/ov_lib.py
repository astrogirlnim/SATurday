"""Overlapping subcube families, p=2, C_D=0 (follows kt_opt.py).  Family: g_j = [x_{S_j}=0], S_j in F (rho-subsets, may overlap).
After rounds q_k = c_k . g (c_k in F_2^s), survivors = {x : some g_j(x)=1 and all q_k(x)=0}.  c_t(K) = GF(2) rank of V_K on survivors."""
import itertools, math, random
import numpy as np

def gf2_rank(rows):
    basis = {}; r = 0
    for x in rows:
        while x:
            h = x.bit_length() - 1
            if h in basis: x ^= basis[h]
            else: basis[h] = x; r += 1; break
    return r

def NK(m, k): return sum(math.comb(m, j) for j in range(k + 1)) if k >= 0 else 0

class Fam:
    def __init__(self, n, sets, K):
        self.n, self.sets, self.K = n, list(sets), K
        self.s = len(self.sets); N = 1 << n; pts = np.arange(N)
        self.G = np.array([(pts & S) == 0 for S in self.sets])            # s x N bool, g_j(x)
        self.base = self.G.any(0)
        ms = [m for m in range(N) if bin(m).count('1') <= K]
        self.vals = np.array([(pts & m) == m for m in ms])                # N(K) x N
        self.rho = bin(self.sets[0]).count('1')
        self.cache = {}
    def rank_keep(self, keep):
        key = np.packbits(keep).tobytes()
        if key in self.cache: return self.cache[key]
        sub = np.packbits(self.vals[:, keep], axis=1)
        r = gf2_rank([int.from_bytes(x.tobytes(), 'big') for x in sub])
        self.cache[key] = r; return r
    def Q(self, c): return (c.astype(np.int64) @ self.G.astype(np.int64)) % 2 == 1   # c: 0/1 vector length s
    def rank_of(self, cs):
        keep = self.base.copy()
        for c in cs: keep &= ~self.Q(c)
        return self.rank_keep(keep)
    def theta1(self): return NK(self.n - self.rho, self.K - self.rho) / NK(self.n, self.K)
    def pang(self): return 0.5 * NK(self.n, self.K - self.rho) / NK(self.n, self.K)

def pair_sets(n): return [(1 << i) | (1 << j) for i, j in itertools.combinations(range(n), 2)]
def triple_sets(n): return [sum(1 << i for i in t) for t in itertools.combinations(range(n), 3)]
def random_sets(n, rho, s, seed):
    rnd = random.Random(seed); allc = list(itertools.combinations(range(n), rho)); rnd.shuffle(allc)
    return [sum(1 << i for i in t) for t in allc[:s]]

def sparse_sets(kind, n, seed=1):
    """sparse overlapping families.  kind: cycle (pairs of C_n), cubic (random 3-regular graph edges), rg<s> (s random pairs),
    sts (Steiner triple system on n=7,9,13,15 : triples pairwise meeting in <=1 point), rt<s> (s random triples)."""
    import networkx as nx
    if kind == 'cycle': return [(1 << i) | (1 << ((i + 1) % n)) for i in range(n)]
    if kind == 'cubic':
        G = nx.random_regular_graph(3, n, seed=seed); return [(1 << u) | (1 << v) for u, v in G.edges()]
    if kind.startswith('rg'): return random_sets(n, 2, int(kind[2:]), seed)
    if kind.startswith('rt'): return random_sets(n, 3, int(kind[2:]), seed)
    if kind == 'sts':
        # Bose/Skolem-free simple construction: greedy random maximal partial STS (linear 3-uniform hypergraph), seeded
        rnd = random.Random(seed); used = set(); out = []
        allt = list(itertools.combinations(range(n), 3)); rnd.shuffle(allt)
        for t in allt:
            ps = [(t[0], t[1]), (t[0], t[2]), (t[1], t[2])]
            if not any(p in used for p in ps):
                used.update(ps); out.append(sum(1 << i for i in t))
        return out
    raise ValueError(kind)
