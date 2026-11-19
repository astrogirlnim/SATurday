"""Representation cost of the cut-state function: minimum number s of terms (each an AND of <= t F_p-affine-equation atoms or their negations,
over Boolean inputs) whose OR equals the target, for target = [sum of k bits is odd] (use p=3) or [sum of k bits == 0 mod 3] (use p=2).
This is the 'line' a partial-sum (cut-by-cut) Tseitin proof needs.  Exact set cover by SAT.  usage: d1_rep.py p target t kmin kmax
target in {parity, mod3}."""
import sys, itertools, time
import numpy as np
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

def run(p, target, t, k, verbose=True):
    N = 2 ** k; X = np.array(list(itertools.product((0, 1), repeat=k)), dtype=np.int64)
    s_ = X.sum(1)
    F = (s_ % 2 == 1) if target == 'parity' else (s_ % 3 == 0)
    atoms = []
    for a in itertools.product(range(p), repeat=k):
        nz = [x for x in a if x]
        if not nz or nz[0] != 1: continue
        val = (X @ np.array(a)) % p
        for b in range(p): atoms.append(val == b)
    A = np.array(atoms); A = np.concatenate([A, ~A])
    A = np.unique(A, axis=0)
    Fp = F[None, :]
    # restrict to atoms that are not trivially false (empty)
    A = A[A.any(1)]
    cand = [A[(A & ~Fp).sum(1) == 0]]    # t=1 terms inside F
    base = A   # unfiltered conjunctions of exactly <= tt atoms (nonempty), deduplicated
    for tt in range(2, t + 1):
        out = []; nb = []
        for i in range(len(A)):
            T = base & A[i][None, :]
            nz = T.any(1)
            T = T[nz]
            if len(T): nb.append(np.unique(T, axis=0))
            ok = ~((T & ~Fp).any(1))
            if ok.any(): out.append(T[ok])
        base = np.unique(np.concatenate(nb + [base]), axis=0)
        if out: cand.append(np.unique(np.concatenate(out), axis=0))
    C = np.unique(np.concatenate(cand), axis=0)
    # dominance pruning: keep maximal terms
    C = C[np.argsort(-C.sum(1))]
    keep = []
    Cb = [int(''.join('1' if x else '0' for x in row), 2) for row in C]
    kept = []
    if len(Cb) <= 6000:
        for i, b in enumerate(Cb):
            if any((b & ~kb) == 0 for kb in kept): continue
            kept.append(b); keep.append(i)
        C = C[keep]
    # set cover: minimum number of rows of C covering F
    pts = list(np.nonzero(F)[0])
    cover = {x: [j for j in range(len(C)) if C[j][x]] for x in pts}
    if any(not v for v in cover.values()): return None, len(C)
    for s in range(1, len(pts) + 1):
        cl = [v for v in cover.values()]
        card = CardEnc.atmost(lits=list(range(1, len(C) + 1)), bound=s, top_id=len(C), encoding=EncType.seqcounter)
        S = Cadical153(bootstrap_with=[[j + 1 for j in v] for v in cl] + card.clauses)
        if S.solve(): return s, len(C)
    return None, len(C)

if __name__ == '__main__':
    p, target, t, k0, k1 = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    for k in range(k0, k1 + 1):
        t0 = time.time(); s, nc = run(p, target, t, k)
        print(f'p={p} target={target} t<={t} k={k}: min terms s = {s}  (maximal candidate terms {nc}, {time.time()-t0:.1f}s)', flush=True)
