import sys, random, numpy as np
from r3lib import *
from r3_e4 import *
# first-round best gain vs exact single-term kernel fraction, block family, larger n
n=int(sys.argv[1]); p=int(sys.argv[2]); cube=Cube(n,p); rnd=random.Random(3)
for rho in (1,2,3):
    gs=blocks(n,rho,cube,rnd)
    for K in (2,3,4):
        B=cube.Vbasis(K); P=np.ones(cube.N,dtype=np.int64)
        c0=fast_rank(cube,B,P,gs); s=len(gs)
        best=c0
        combos=span_combos(s,p) 
        cand=[tuple(1 if j==i else 0 for j in range(s)) for i in range(s)]+rnd.sample(combos,min(40,len(combos)))
        for co in cand:
            best=min(best,fast_rank(cube,B,P*Pprime(cube,gs,co),gs))
        z=NK(n-rho,K-rho)  # dim of f supported on one subcube
        print(f"n={n} p={p} rho={rho} s={s} K={K}: c0={c0} best c1={best} gain={(c0-best)/c0:.4f}  z/N(K)={z/NK(n,K):.4f}  (K/n)^rho={(K/n)**rho:.4f}  PangEta={(1-1/p)*NK(n,max(K-(p-1)*rho,0))/NK(n,K) if K>=(p-1)*rho else float('nan'):.4f}",flush=True)
