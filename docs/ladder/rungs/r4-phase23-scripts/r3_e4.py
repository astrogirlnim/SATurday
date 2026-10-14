import sys, random, math, numpy as np
from r3lib import *
from math import comb
def NK(n,K):
    if n<=60: return sum(comb(n,j) for j in range(0,K+1))
    # float: sum of binomials via ratio recursion (log-scale safe)
    t=1.0; tot=1.0; 
    for j in range(1,K+1):
        t*= (n-j+1)/j; tot+=t
    return tot
def flat_table():
    print("flatness c_g(K-rho)/c_g(K) for single subcube g of codim rho (C=0), c_g(K)=N_{n-rho}(K)  [PROVED-BY-HAND formula]")
    for n,K in ((12,3),(100,10),(1000,63)):
        out=[]
        for rho in (1,2,4,8,16,32,64):
            if rho>K: continue
            r=NK(n-rho,K-rho)/NK(n-rho,K)
            out.append(f"rho={rho}: {r:.3e}")
        print(f" n={n} K={K}(=n/16): "+", ".join(out))
def fast_rank(cube,B,P,gs):
    U=np.zeros(cube.N,dtype=bool)
    for g in gs: U|=((P*g)!=0)
    return rank_mod(B[:,np.nonzero(U)[0]],cube.p)
def greedy0(cube,K,gs,rnd,ncomb=60,maxr=60):
    p=cube.p; s=len(gs); B=cube.Vbasis(K)
    P=np.ones(cube.N,dtype=np.int64); c=[fast_rank(cube,B,P,gs)]
    combos=span_combos(s,p)
    while c[-1]>0 and len(c)<=maxr:
        cs=combos if len(combos)<=ncomb else rnd.sample(combos,ncomb)
        best=None
        for co in cs:
            P2=P*Pprime(cube,gs,co); r=fast_rank(cube,B,P2,gs)
            if best is None or r<best[0]: best=(r,P2)
        if best[0]>=c[-1] and len(c)>1: break
        c.append(best[0]); P=best[1]
    return c
def blocks(n,rho,cube,rnd,s=None):
    s=s or n//rho; gs=[]
    for i in range(s):
        vs=list(range(i*rho,(i+1)*rho)); a=[]
        gs.append(cube.indicator([([1 if j==v else 0 for j in range(n)],0) for v in vs]))
    return gs
if __name__=='__main__':
    flat_table()
    n=int(sys.argv[1]); p=int(sys.argv[2])
    cube=Cube(n,p); rnd=random.Random(5)
    print(f"\nblock family (disjoint subcubes x_B=0), n={n} p={p}, greedy best-q rounds, C=0")
    for rho in (1,2,3,4):
        for K in (2,3,4):
            gs=blocks(n,rho,cube,rnd)
            c=greedy0(cube,K,gs,rnd)
            t=len(c)-1; d=(p-1)*rho
            geo=1-(max(c[-1],1)/c[0])**(1/t) if t else float('nan')
            etaP=(1-1/p)*NK(n,max(K-d,0))/NK(n,K) if K>=d else float('nan')
            print(f" rho={rho} s={len(gs)} K={K}: c={c}  rounds={t} geo-rate={geo:.3f} firstgain={(1-c[1]/c[0]) if t else 0:.3f} PangEta={etaP:.4f}")
