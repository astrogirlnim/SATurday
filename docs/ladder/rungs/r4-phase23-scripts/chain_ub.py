import networkx as nx, random, numpy as np, math, sys
from tmodel import ball_ok
from functools import lru_cache
@lru_cache(maxsize=None)
def rad(a0,a1,a2):
    s=a0+a1+a2; F=np.arange(0,s+1)
    def feas(D):
        lb=[np.maximum(0,-((-(a+F-D))//2)) for a in (a0,a1,a2)]
        ok=(lb[0]<=a0)&(lb[1]<=a1)&(lb[2]<=a2)&(lb[0]+lb[1]+lb[2]<=F)
        return bool(ok.any())
    lo,hi=0,s
    while lo<hi:
        m=(lo+hi)//2
        if feas(m): hi=m
        else: lo=m+1
    return lo
def chain_ub(G,order):
    pos={v:i for i,v in enumerate(order)}; d=max(dict(G.degree()).values())
    cur=0; best=d
    for v in order:
        back=sum(1 for u in G[v] if pos[u]<pos[v]); fwd=G.degree(v)-back
        a0=back; a1=cur-back; a2=fwd
        best=max(best,rad(a0,a1,a2)); cur+= fwd-back
    return best
def best_order(G,tries,rng):
    # greedy: repeatedly add vertex minimizing resulting cut; start random
    bestub=10**9
    for t in range(tries):
        nodes=list(G.nodes()); rng.shuffle(nodes)
        if t%2==0: order=nodes
        else:
            order=[nodes[0]]; S={nodes[0]}; 
            cand=set(G[nodes[0]])
            while len(order)<len(nodes):
                pool=cand if cand else set(nodes)-S
                v=min(pool,key=lambda v:(G.degree(v)-2*sum(1 for u in G[v] if u in S),rng.random()))
                order.append(v); S.add(v); cand|=set(G[v]); cand-=S
        ub=chain_ub(G,order); bestub=min(bestub,ub)
    return bestub
if __name__=="__main__":
    rng=random.Random(1)
    print("V d n=E chainUB UB/n  (bisection lower est ~ E/2 - V*sqrt(d ln2)/2)")
    for V,d in [(14,9),(14,6),(20,6),(30,6),(30,10),(60,6),(60,12),(100,8),(100,16),(100,32),(200,16),(200,40),(300,24)]:
        G=nx.random_regular_graph(d,V,seed=5); E=G.number_of_edges()
        ub=best_order(G,6 if V<=100 else 3,rng)
        print(V,d,E,ub,round(ub/E,3),"  Eover4=",E//4,"  naive_cutwidth/E bound=0.5",flush=True)
