"""Combinatorial model of the exact multilinear PC degree of Tseitin-mod-2 over F_p (p odd),
derived by hand (see r4-phase23-program.md, Section 2).  Vertex sets U (mod complement) <-> cut
vectors T=delta(U) in F_2^E.  Start: singletons (needs deg d<=D).  Compose U1,U2 -> U1 xor U2 iff
the three Hamming balls of radius D around 0, T1, T2 have a common point.  Refuted iff some cut
vector T is derived from both U and its complement."""
import numpy as np, itertools, random
POP=np.array([bin(i).count('1') for i in range(256)],dtype=np.int64)
def pop(a):  # a: uint64 array
    b=a.view(np.uint8).reshape(a.shape+(8,))
    return POP[b].sum(axis=-1)
def ball_ok(a0,a1,a2,D):
    """exists flips f_i in [0,a_i] with d_i<=D, d0=a0-f0+f1+f2 etc.  vectorized over arrays"""
    ok=np.zeros(a0.shape,dtype=bool)
    smax=int((a0+a1+a2).max()) if a0.size else 0
    for F in range(0,min(smax,3*D)+1):
        lb0=np.maximum(0,-((-(a0+F-D))//2)); lb1=np.maximum(0,-((-(a1+F-D))//2)); lb2=np.maximum(0,-((-(a2+F-D))//2))
        good=(lb0<=a0)&(lb1<=a1)&(lb2<=a2)&(lb0+lb1+lb2<=F)&(F<=a0+a1+a2)
        ok|=good
    return ok
def tseitin_pc_degree(edges,V,Dmax=None):
    E=len(edges); assert E<=64
    cut=[0]*V
    for k,(a,b) in enumerate(edges): cut[a]|=1<<k; cut[b]|=1<<k
    dmax=max(bin(c).count('1') for c in cut)
    for D in range(dmax,(Dmax or E)+1):
        if refutes(cut,V,D): return D
    return None
def refutes(cut,V,D):
    full=(1<<V)-1
    def Tof(U):
        t=0
        for v in range(V):
            if U>>v&1: t^=cut[v]
        return t
    Tmap={}  # T -> U
    Ws=[];Ts=[]
    queue=[]
    for v in range(V):
        U=1<<v; T=cut[v]
        if T in Tmap: 
            if Tmap[T]!=U: return True
            continue
        Tmap[T]=U; Ws.append(U); Ts.append(T)
    i=0
    while i<len(Ws):
        U1=Ws[i]; T1=Ts[i]; i+=1
        if i<=1 and False: pass
        Tarr=np.array(Ts[:i],dtype=np.uint64); Uarr=np.array(Ws[:i],dtype=np.uint64)
        Tn=np.uint64(T1)
        a0=pop(Tarr&Tn); a1=pop(Tn&~Tarr); a2=pop(Tarr&~Tn)
        ok=ball_ok(a0,a1,a2,D)
        for j in np.nonzero(ok)[0]:
            U3=U1^int(Uarr[j])
            if U3==0 or U3==full: 
                # T=empty: derived from U=0 and U=V (complements): contradiction iff both signs;  U3 in {0,V}
                if U3==full: return True
                continue
            T3=T1^Ts[j]
            if T3 in Tmap:
                if Tmap[T3]!=U3: return True
            else:
                Tmap[T3]=U3; Ws.append(U3); Ts.append(T3)
    return False
