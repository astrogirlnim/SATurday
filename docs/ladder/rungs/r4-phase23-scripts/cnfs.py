import itertools, random
from pcdeg import *
def tseitin_mod2(edges,V,charge,p):
    """vertex constraint: sum of incident x_e == charge mod 2 ; axioms = forbidden assignments"""
    n=len(edges); ax=[]
    for v in range(V):
        inc=[k for k,(a,b) in enumerate(edges) if v in (a,b)]
        for asg in itertools.product([0,1],repeat=len(inc)):
            if sum(asg)%2!=charge[v]: ax.append(forbid_poly(inc,asg,p))
    return n,ax
def tseitin_modq(edges,V,charge,q,p):
    """Boolean edge variable, edge oriented a->b: contributes +x to a, -x to b; constraint sum == charge mod q"""
    n=len(edges); ax=[]
    for v in range(V):
        inc=[(k,1 if edges[k][0]==v else -1) for k,(a,b) in enumerate(edges) if v in (a,b)]
        for asg in itertools.product([0,1],repeat=len(inc)):
            if sum(s*x for (k,s),x in zip(inc,asg))%q!=charge[v]%q: ax.append(forbid_poly([k for k,_ in inc],asg,p))
    return n,ax
def rand3cnf(n,m,p,seed):
    rnd=random.Random(seed); ax=[]
    for _ in range(m):
        vs=rnd.sample(range(n),3); sg=[rnd.randint(0,1) for _ in vs]
        ax.append(forbid_poly(vs,[1-s for s in sg],p))  # clause falsified by x=1-sign
    return n,ax
def complete(V): return [(a,b) for a in range(V) for b in range(a+1,V)]
