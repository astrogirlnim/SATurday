"""Exact polynomial calculus (PC) degree over F_p for Boolean (0/1) variables, small n.
PC degree D := least D such that 1 lies in the smallest subspace S of V_D (multilinear polys
of degree <= D) containing the axioms and closed under: g in S, deg(x_i*g) <= D (after x^2=x
reduction)  =>  x_i*g in S.  (Boolean axioms are implicit.)  Computed by fixpoint iteration
with dense linear algebra mod p.  Also: Nullstellensatz-style degree (span of m*f with
deg(m*f)<=D, reduced) for comparison.   Intended for n <= ~13.
"""
import itertools, sys, numpy as np

def inv(a,p): return pow(int(a),p-2,p)

def rref(M,p):
    """row-reduce mod p; returns (R, pivots) with zero rows dropped"""
    M=M.copy()%p; r=0; piv=[]
    rows,cols=M.shape
    for c in range(cols):
        if r>=rows: break
        nz=np.nonzero(M[r:,c])[0]
        if nz.size==0: continue
        k=r+nz[0]
        if k!=r: M[[r,k]]=M[[k,r]]
        M[r]=(M[r]*inv(M[r,c],p))%p
        idx=np.nonzero(M[:,c])[0]; idx=idx[idx!=r]
        if idx.size: M[idx]=(M[idx]-np.outer(M[idx,c],M[r]))%p
        piv.append(c); r+=1
    return M[:r],piv

class Space:
    def __init__(s,n,D):
        s.n=n; s.D=D
        masks=[m for m in range(1<<n) if bin(m).count('1')<=D]
        masks.sort(key=lambda m:(-bin(m).count('1'),m))
        s.masks=masks; s.idx={m:i for i,m in enumerate(masks)}; s.N=len(masks)
        s.deg=np.array([bin(m).count('1') for m in masks])
        # multiplication-by-x_i column maps
        s.mul=[np.array([s.idx.get(m|(1<<i),-1) for m in masks]) for i in range(n)]
    def mulrows(s,R,i,p):
        out=np.zeros_like(R); tgt=s.mul[i]
        ok=tgt>=0
        # monomials whose product exceeds degree D: coefficient must be 0 (caller guarantees)
        np.add.at(out.T,tgt[ok],R[:,ok].T)
        return out%p

def poly_vec(sp,poly,p):
    v=np.zeros(sp.N,dtype=np.int64)
    for m,c in poly.items(): v[sp.idx[m]]=c%p
    return v

def mul_poly(a,b,p):
    out={}
    for m1,c1 in a.items():
        for m2,c2 in b.items():
            m=m1|m2; out[m]=(out.get(m,0)+c1*c2)%p
    return {m:c for m,c in out.items() if c}

def lit_poly(i,val,p):  # indicator that x_i==val
    return {(1<<i):1,0:0} if val==1 else {0:1,(1<<i):p-1}

def forbid_poly(vars_,assign,p):
    """polynomial = 1 iff x_vars == assign (so the axiom says this assignment is forbidden)"""
    poly={0:1}
    for v,a in zip(vars_,assign):
        poly=mul_poly(poly,lit_poly(v,a,p),p)
    return {m:c for m,c in poly.items() if c}

def has_one(S,sp):
    # S is in rref with columns ordered by decreasing degree; e_empty in S iff a row has its pivot in the last column
    if not S.shape[0]: return False
    r=S[-1]; nz=np.nonzero(r)[0]
    return nz.size==1 and nz[0]==sp.N-1

def pc_closure_has_one(n,axioms,D,p,verbose=False):
    sp=Space(n,D)
    if max(bin(m).count('1') for a in axioms for m in a)>D: return False
    A=np.array([poly_vec(sp,a,p) for a in axioms])
    S,piv=rref(A,p)
    top=sp.deg==D
    while True:
        if has_one(S,sp): return True
        lead=np.array([sp.deg[c] for c in piv])
        new=[]
        low=S[lead<D]; hi=S[lead==D]
        for i in range(n):
            if low.shape[0]: new.append(sp.mulrows(low,i,p))
            if hi.shape[0]:
                cols=[c for c in np.nonzero(top)[0] if not (sp.masks[c]>>i)&1]
                if not cols: comb=hi
                else:
                    Amat=hi[:,cols]; t=hi.shape[0]
                    aug=np.concatenate([Amat,np.eye(t,dtype=np.int64)],axis=1)
                    R,pv=rref(aug,p)
                    ker=R[[k for k in range(R.shape[0]) if not R[k,:len(cols)].any()]][:,len(cols):]
                    # rows of R beyond echelon rank with zero A-part: left kernel
                    if ker.shape[0]==0: continue
                    comb=(ker@hi)%p
                new.append(sp.mulrows(comb,i,p))
        if not new: return False
        S2,piv2=rref(np.concatenate([S]+new),p)
        if S2.shape[0]==S.shape[0]: return False
        S,piv=S2,piv2

def ns_has_one(n,axioms,D,p):
    """Nullstellensatz-style: span of m*f (m multilinear, reduced degree of product <= D)"""
    sp=Space(n,D); rows=[]
    for a in axioms:
        for m in range(1<<n):
            q=mul_poly(a,{m:1},p)
            if q and max(bin(k).count('1') for k in q)<=D: rows.append(poly_vec(sp,q,p))
    if not rows: return False
    S,_=rref(np.array(rows),p)
    return has_one(S,sp)

def pc_degree(n,axioms,p,method='pc',Dmin=1,Dmax=None):
    f=pc_closure_has_one if method=='pc' else ns_has_one
    for D in range(max(Dmin,max(bin(m).count('1') for a in axioms for m in a)),(Dmax or n)+1):
        if f(n,axioms,D,p): return D
    return None
