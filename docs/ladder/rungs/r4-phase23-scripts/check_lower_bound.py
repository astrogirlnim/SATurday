import networkx as nx, math, numpy as np
from tmodel import tseitin_pc_degree
bad=0;tot=0;rows=[]
for V in range(6,15):
    for d in range(3,V):
        if V*d%2 or V*d//2>64: continue
        for seed in range(2):
            G=nx.random_regular_graph(d,V,seed=seed)
            if not nx.is_connected(G): continue
            e=list(G.edges()); E=len(e)
            idx=np.arange(1<<V); cut=np.zeros(1<<V,dtype=np.int64)
            for a,b in e: cut+=((idx>>a)^(idx>>b))&1
            sz=np.array([bin(i).count('1') for i in range(1<<V)])
            mid=(3*sz>=V)&(3*sz<=2*V)
            b13=int(cut[mid].min()); D=tseitin_pc_degree(e,V)
            lb=max(d,math.ceil(b13/2)); tot+=1
            if D<lb: bad+=1; print("VIOLATION",V,d,seed,D,lb)
            rows.append((V,d,E,D,b13,lb))
print("checked",tot,"violations",bad)
import collections
print("tight (D==lb):",sum(1 for r in rows if r[3]==r[5]),"of",len(rows))
for r in rows[-12:]: print(r)
