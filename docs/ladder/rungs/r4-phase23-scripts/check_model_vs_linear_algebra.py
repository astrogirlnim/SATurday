from cnfs import *
from tmodel import *
import time
def Q3(): return [(a,a^(1<<i)) for a in range(8) for i in range(3) if a<a^(1<<i)],8
tests={"C3":(complete(3),3),"K4":(complete(4),4),"K5":(complete(5),5),"K33":([(a,3+b) for a in range(3) for b in range(3)],6),"Q3":Q3(),
 "octa":([(a,b) for a in range(6) for b in range(a+1,6) if b-a!=3],6),
 "C5":([(i,(i+1)%5) for i in range(5)],5),"prism":([(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)],6),
 "K4x2":(complete(4)+complete(4),4)}
for k,(e,V) in tests.items():
    t=time.time(); m=tseitin_pc_degree(e,V)
    n,ax=tseitin_mod2(e,V,[1]+[0]*(V-1),3)
    la=pc_degree(n,ax,3) if n<=12 else None
    print(k,"n",n,"model",m,"LA",la,round(time.time()-t,2),flush=True)
