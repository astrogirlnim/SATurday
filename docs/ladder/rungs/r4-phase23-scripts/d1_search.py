"""D1 search: shortest refutation of Tseitin_q (one-hot / Z_q-valued edges) in a semantic depth-2 AC0[p]-style line system.
See r4-d1-search.md Sec 1 for the exact system.  SAT encoding with unknown lines (pysat Cadical153; run each m under an external timeout).

System S(p, s, t, atoms):  points = Z_q^E (the one-hot-valid cube).  A line is a function on the cube of the form
   OR_{r<s} AND_{c<t} atom_{r,c}        (each term may be switched off, each atom may be switched to TRUE)
   atom = [ sum_e A[e][x_e] = b (mod p) ]  or its negation        (mode 'lin': a MOD_p gate / F_p-affine equation over one-hot vars)
   atom = [ x_e = v ] or its negation                              (mode 'lit': a literal)
Derivation: line i is implied (pointwise on the cube) by two earlier lines or axioms; the last line is the constant 0.
Size = number of derived lines (axioms are free).  Semantic rule => weakening, cut, AND-intro, MOD rules are all special cases,
so the minimum here lower-bounds every syntactic system with the same line class.
"""
import itertools, sys, time
import numpy as np
import networkx as nx
from pysat.solvers import Cadical153

def graph(name):
    if name == 'K4': G = nx.complete_graph(4)
    elif name == 'K5': G = nx.complete_graph(5)
    elif name == 'K33': G = nx.complete_bipartite_graph(3, 3)
    elif name == 'prism': G = nx.circular_ladder_graph(3)
    elif name == 'Q3': G = nx.hypercube_graph(3); G = nx.convert_node_labels_to_integers(G)
    elif name.startswith('ladder'): G = nx.ladder_graph(int(name[6:]))
    elif name.startswith('cyc'): G = nx.cycle_graph(int(name[3:]))
    elif name.startswith('cub'):  # cubic random regular, cub<V>_<seed>
        v, sd = name[3:].split('_'); G = nx.random_regular_graph(3, int(v), seed=int(sd))
    else: raise ValueError(name)
    return G

def tseitin(G, q):
    """edges oriented u->v (u<v); vertex 0 has charge 1; returns edges, points (N x E int array), axioms (list of bool arrays)."""
    edges = sorted((min(u, v), max(u, v)) for u, v in G.edges()); E = len(edges)
    pts = np.array(list(itertools.product(range(q), repeat=E)), dtype=np.int8)
    ax = []
    for v in sorted(G.nodes()):
        inc = [(k, (1 if edges[k][0] == v else -1)) for k in range(E) if v in edges[k]]
        c = 1 if v == min(G.nodes()) else 0
        for loc in itertools.product(range(q), repeat=len(inc)):
            if sum(sg * a for (k, sg), a in zip(inc, loc)) % q != c:   # violating local assignment -> clause forbidding it
                ok = np.zeros(len(pts), bool)
                for (k, sg), a in zip(inc, loc): ok |= (pts[:, k] != a)
                ax.append(ok)
    return edges, pts, ax

class Enc:
    def __init__(self): self.n = 0; self.cl = []
    def new(self): self.n += 1; return self.n
    def add(self, *c): self.cl.append(list(c))
    def exactly_one(self, vs):
        self.cl.append(list(vs))
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)): self.cl.append([-vs[i], -vs[j]])

def build(G, q, p, s, t, m, mode='lin', neg=True, symbreak=True):
    edges, pts, ax = tseitin(G, q); E = len(edges); N = len(pts); A = len(ax)
    e = Enc(); TRUE = e.new(); e.add(TRUE)
    # trie over prefixes of the point tuple
    # node = (k, prefix tuple); leaves are points
    def atom_eq(info):
        """returns list eq[x] of literals (var ids) giving atom truth on each point; records decoding info in dict"""
        if mode == 'lit':
            sel = {(k, v): e.new() for k in range(E) for v in range(q)}
            e.exactly_one(list(sel.values())); info['sel'] = sel
            eq = []
            for x in range(N):
                z = e.new(); lits = [sel[(k, int(pts[x, k]))] for k in range(E)]
                e.add(-z, *lits)
                for l in lits: e.add(-l, z)
                eq.append(z)
            return eq
        a = {(k, v): [e.new() for _ in range(p)] for k in range(E) for v in range(q)}
        for vs in a.values(): e.exactly_one(vs)
        b = [e.new() for _ in range(p)]; e.exactly_one(b); info['a'] = a; info['b'] = b
        st = {(): [TRUE] + [-TRUE] * (p - 1)}   # constants: state 0
        # build trie levels
        for k in range(E):
            for pre in itertools.product(range(q), repeat=k):
                for v in range(q):
                    node = pre + (v,); sv = [e.new() for _ in range(p)]; st[node] = sv
                    for u in range(p):
                        for c in range(p):
                            e.add(-st[pre][u], -a[(k, v)][c], sv[(u + c) % p])
        eq = []
        for x in range(N):
            leaf = st[tuple(int(y) for y in pts[x])]; z = e.new()
            for u in range(p):
                for w in range(p):
                    e.add(-leaf[u], -b[w], z if u == w else -z)
            eq.append(z)
        return eq
    lines = []; infos = []
    for i in range(m):
        terms = []; tinfo = []
        for r in range(s):
            off = e.new(); lits = []; ainfo = []
            for c in range(t):
                info = {}; eq = atom_eq(info)
                triv = e.new(); ng = e.new() if neg else None
                if not neg: e.add(-ng if ng else TRUE)
                L = []
                for x in range(N):
                    f = e.new()
                    if neg:   # f = eq xor ng
                        e.add(-eq[x], -ng, -f); e.add(eq[x], ng, -f); e.add(-eq[x], ng, f); e.add(eq[x], -ng, f)
                    else: e.add(-eq[x], f); e.add(eq[x], -f)
                    l = e.new(); e.add(-triv, l); e.add(-f, l); e.add(triv, f, -l)
                    L.append(l)
                lits.append(L); ainfo.append((info, triv, ng))
            T = []
            for x in range(N):
                z = e.new()
                for L in lits: e.add(-z, L[x])
                e.add(-off, -z); e.add(off, *[-L[x] for L in lits], z)
                T.append(z)
            terms.append(T); tinfo.append((off, ainfo))
        Ti = []
        for x in range(N):
            z = e.new()
            for T in terms: e.add(-T[x], z)
            e.add(-z, *[T[x] for T in terms]); Ti.append(z)
        lines.append(Ti); infos.append(tinfo)
    axc = [[(TRUE if a[x] else -TRUE) for x in range(N)] for a in ax]
    sels = []
    for i in range(m):
        cand = axc + lines[:i]; pr = []
        for side in range(2):
            ps = [e.new() for _ in cand]; e.exactly_one(ps)
            U = [e.new() for _ in range(N)]
            for j, pj in enumerate(ps):
                for x in range(N):
                    e.add(-pj, -U[x], cand[j][x]); e.add(-pj, U[x], -cand[j][x])
            pr.append((ps, U))
        for x in range(N): e.add(-pr[0][1][x], -pr[1][1][x], lines[i][x])
        sels.append((pr[0][0], pr[1][0]))
    if symbreak:
        # canonical topological order by depth: lev_i > lev_j for each chosen derived premise j, lev nondecreasing in i; every line but the last is used
        L = m
        lev = [[None] + [e.new() for _ in range(1, L)] for _ in range(m)]   # lev[i][k] <=> level_i >= k
        for i in range(m):
            for k in range(2, L): e.add(-lev[i][k], lev[i][k - 1])
            if i: 
                for k in range(1, L): e.add(-lev[i - 1][k], lev[i][k])
        for i in range(m):
            for side in range(2):
                for jj in range(i):
                    pj = sels[i][side][A + jj]
                    e.add(-pj, lev[i][1]) if L > 1 else e.add(-pj)
                    for k in range(1, L):
                        if k + 1 < L: e.add(-pj, -lev[jj][k], lev[i][k + 1])
                        else: e.add(-pj, -lev[jj][k])
        for jj in range(m - 1):
            e.add(*[sels[i][side][A + jj] for i in range(jj + 1, m) for side in range(2)])
    for x in range(N): e.add(-lines[m - 1][x])
    return e, dict(edges=edges, pts=pts, ax=ax, lines=lines, infos=infos, sels=sels, q=q, p=p, mode=mode, neg=neg)

def verify(model, D):
    """independent re-evaluation of the decoded proof."""
    val = set(l for l in model if l > 0); pts = D['pts']; N = len(pts); q = D['q']; p = D['p']
    tabs = [np.array([x in val for x in Ti]) for Ti in D['lines']]
    for i, tinfo in enumerate(D['infos']):
        out = np.zeros(N, bool)
        for off, ainfo in tinfo:
            if off in val: continue
            term = np.ones(N, bool)
            for info, triv, ng in ainfo:
                if triv in val: continue
                if D['mode'] == 'lit':
                    (k, v), = [kv for kv, z in info['sel'].items() if z in val]; ev = pts[:, k] == v
                else:
                    ssum = np.zeros(N, int)
                    for (k, v), vs in info['a'].items():
                        c = [j for j in range(p) if vs[j] in val][0]; ssum += (pts[:, k] == v) * c
                    bb = [j for j in range(p) if info['b'][j] in val][0]; ev = (ssum % p) == bb
                term &= (~ev if ng in val else ev)
            out |= term
        assert (out == tabs[i]).all(), 'line eval mismatch'
        sA, sB = D['sels'][i]; cand = D['ax'] + tabs[:i]
        ja = [j for j, v in enumerate(sA) if v in val][0]; jb = [j for j, v in enumerate(sB) if v in val][0]
        assert not (cand[ja] & cand[jb] & ~tabs[i]).any(), 'not implied'
    assert not tabs[-1].any(); return tabs

def describe(model, D):
    val = set(l for l in model if l > 0); p = D['p']; out = []
    for i, tinfo in enumerate(D['infos']):
        ts = []
        for off, ainfo in tinfo:
            if off in val: continue
            at = []
            for info, triv, ng in ainfo:
                if triv in val: continue
                if D['mode'] == 'lit':
                    (k, v), = [kv for kv, z in info['sel'].items() if z in val]; s_ = f'x{k}={v}'
                else:
                    co = {}
                    for (k, v), vs in info['a'].items():
                        c = [j for j in range(p) if vs[j] in val][0]
                        if c: co[(k, v)] = c
                    bb = [j for j in range(p) if info['b'][j] in val][0]
                    s_ = '[' + '+'.join(f'{c}*x{k}={v}' for (k, v), c in sorted(co.items())) + f' == {bb}]'
                at.append(('~' if ng in val else '') + s_)
            ts.append(' & '.join(at) if at else 'T')
        out.append(' | '.join(ts) if ts else 'F')
    return out

def solve(Gname, q, p, s, t, m, mode='lin', neg=True, limit=0, quiet=False):
    G = graph(Gname); t0 = time.time(); e, D = build(G, q, p, s, t, m, mode, neg)
    S = Cadical153(bootstrap_with=e.cl); ok = S.solve(); dt = time.time() - t0
    if not ok: return 'UNSAT', dt, None
    r = S.get_model(); verify(r, D); return 'SAT', dt, describe(r, D)

def minimal(Gname, q, p, s, t, mode='lin', mmax=40, mmin=1, limit=0, neg=True, verbose=True):
    res = {}
    for m in range(mmin, mmax + 1):
        st, dt, d = solve(Gname, q, p, s, t, m, mode, neg, limit)
        if verbose: print(f'  {Gname} q={q} p={p} s={s} t={t} {mode} m={m}: {st} {dt:.1f}s', flush=True)
        res[m] = st
        if st == 'SAT': return m, res, d
        if st == 'UNKNOWN': return None, res, None
    return None, res, None

if __name__ == '__main__':
    # usage: d1_search.py GRAPH q p s t mode m   -> solves for exactly m derived lines (run under `timeout`)
    g, q, p, s, t, mode, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], int(sys.argv[7])
    st, dt, d = solve(g, q, p, s, t, m, mode)
    print(f'{g} q={q} p={p} s={s} t={t} {mode} m={m}: {st} {dt:.1f}s', flush=True)
    if d: print('\n'.join(f'  L{i+1}: {l}' for i, l in enumerate(d)))
