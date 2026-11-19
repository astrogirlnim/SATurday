"""Exact minimum DAG-like resolution refutation size (number of derived clauses) of Tseitin_q with Z_q-valued one-hot edges,
over clauses of width <= W.  Clause = partial assignment (tuple of (edge,value)) read as 'NOT(all of these)'; literal = (edge,value)
negated.  Resolution on edge e: from  A v (e!=a)  and  B v (e!=b)... for q=2 this is ordinary resolution.  For q>2 we use the
semantic version over the cube: two clauses g,h (forbidden partial assignments) imply f iff f subsumes... we implement the
cube-semantic closure: forbidden-set view: g forbids box Bg, h forbids box Bh; f implied iff Bf subset of Bg u Bh.
Here boxes are subcubes of Z_q^E; for q=2 this coincides with resolution.  Exact search = SAT over hyperedges + level order + cardinality.
usage: d1_res_exact.py GRAPH q W mmin mmax
"""
import sys, itertools, time
import numpy as np
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from d1_search import graph, tseitin

def run(Gname, q, W, mmin, mmax, tmax=None):
    G = graph(Gname); edges, pts, ax = tseitin(G, q); E = len(edges)
    # clause = frozenset of (edge,value) pairs forbidden jointly; encode as tuple of length E with -1 = free
    def boxes():
        out = []
        for k in range(0, W + 1):
            for es in itertools.combinations(range(E), k):
                for vs in itertools.product(range(q), repeat=k):
                    t = [-1] * E
                    for e_, v in zip(es, vs): t[e_] = v
                    out.append(tuple(t))
        return out
    V = boxes(); idx = {c: i for i, c in enumerate(V)}
    # axioms as boxes
    axb = []
    for v in sorted(G.nodes()):
        inc = [(k, (1 if edges[k][0] == v else -1)) for k in range(E) if v in edges[k]]
        c = 1 if v == min(G.nodes()) else 0
        for loc in itertools.product(range(q), repeat=len(inc)):
            if sum(sg * a for (k, sg), a in zip(inc, loc)) % q != c:
                t = [-1] * E
                for (k, sg), a in zip(inc, loc): t[k] = a
                axb.append(tuple(t))
    axset = set(idx[a] for a in axb)
    # hyperedges: for clauses over q=2 : resolution.  For q>2 use semantic: f derived from g,h if box(f) subset box(g) u box(h):
    # complete rule for boxes: either f subset g, f subset h (weakening: unnecessary), or union of g,h covers f: g,h agree except one coordinate e,
    # where together they cover Z_q (only possible with q=2) ... for q>2 pairs cannot cover; need q boxes (fan-in 2 insufficient) -> only subsumption.
    # So for q>2 the minimum over clause lines is infinite unless some derived line is a 'multi-valued' clause; we only support q=2 here.
    assert q == 2
    hyp = {}   # f -> list of (g,h)
    n = len(V)
    arr = np.array(V, dtype=np.int8)
    for gi in range(n):
        g = arr[gi]
        # candidates h that clash with g on exactly one coord
        diff = (arr != -1) & (g != -1) & (arr != g)
        nd = diff.sum(1)
        for hi in np.nonzero(nd == 1)[0]:
            if hi < gi: continue
            h = arr[hi]; e_ = int(np.nonzero(diff[hi])[0][0])
            r = np.where(g != -1, g, h); r[e_] = -1
            if (r != -1).sum() > W: continue
            f = idx[tuple(int(x) for x in r)]
            hyp.setdefault(f, []).append((gi, int(hi)))
    empty = idx[tuple([-1] * E)]
    # restrict to clauses that can matter: forward reachable from axioms
    reach = set(axset); changed = True
    while changed:
        changed = False
        for f, lst in hyp.items():
            if f in reach: continue
            if any(g in reach and h in reach for g, h in lst): reach.add(f); changed = True
    if empty not in reach: return None
    hyp = {f: [(g, h) for g, h in l if g in reach and h in reach] for f, l in hyp.items() if f in reach and f not in axset}
    nodes = sorted(reach); print(f'  reachable clauses {len(nodes)}, hyperedges {sum(len(l) for l in hyp.values())}', flush=True)
    for m in range(mmin, mmax + 1):
        t0 = time.time(); cnt = [0]
        def nv(): cnt[0] += 1; return cnt[0]
        y = {f: nv() for f in nodes if f not in axset}
        L = m  # levels 0..m-1 ; order enc o[f][k] = lev>=k, k=1..m-1
        o = {f: [None] + [nv() for _ in range(1, L)] for f in y}
        cl = []
        for f in y:
            for k in range(2, L): cl.append([-o[f][k], o[f][k - 1]])
        def lt(g, f, k_cond):  # clauses ensuring lev[g] < lev[f]; axioms level -1 (always ok)
            pass
        for f, lst in hyp.items():
            zs = []
            for (g, h) in lst:
                z = nv(); zs.append(z)
                for u in (g, h):
                    if u in y:   # y[u] true and lev[u] < lev[f]
                        cl.append([-z, y[u]])
                        cl.append([-z, o[f][1]] if L > 1 else [-z])
                        for k in range(1, L):
                            cl.append([-z, -o[u][k], o[f][k + 1]] if k + 1 < L else [-z, -o[u][k]])
            cl.append([-y[f]] + zs)
        cl.append([y[empty]])
        lits = list(y.values())
        card = CardEnc.atmost(lits=lits, bound=m, top_id=cnt[0], encoding=EncType.seqcounter)
        S = Cadical153(bootstrap_with=cl + card.clauses)
        ok = S.solve(); print(f'  {Gname} W={W} resolution m<={m}: {"SAT" if ok else "UNSAT"} {time.time()-t0:.1f}s', flush=True)
        if ok:
            mod = set(l for l in S.get_model() if l > 0); used = [f for f in y if y[f] in mod]
            return m, [V[f] for f in used]
    return None

if __name__ == '__main__':
    g, q, W, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    print(run(g, q, W, a, b))
