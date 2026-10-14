"""Search random 3-CNFs (n vars, m clauses) with exact PC degree >= 5 over F_p.  usage: kt_search.py p n m seeds"""
import sys, time
from pcdeg import *
from cnfs import rand3cnf
p, n, m, S = map(int, sys.argv[1:5])
for seed in range(S):
    nn, ax = rand3cnf(n, m, p, seed); t = time.time()
    if pc_closure_has_one(nn, ax, 4, p):          # degree <= 4: not interesting
        print(f"seed {seed}: deg<=4 ({time.time()-t:.0f}s)", flush=True); continue
    d = pc_degree(nn, ax, p, Dmin=5, Dmax=7)
    print(f"seed {seed}: n={n} m={m} p={p} PC degree {d} ({time.time()-t:.0f}s)", flush=True)
