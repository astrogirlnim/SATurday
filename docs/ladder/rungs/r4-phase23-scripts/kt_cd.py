"""Nontrivial consequence space: PHP (4 pigeons, 3 holes, 12 vars) has PC degree 4 > width 3 over F_2, F_3 (kt_deg.py).
C_3 = PC closure at degree 3 (no 1 inside).  Greedy Pang rounds with and without C_3 on (a) pigeon blocks (the 4 falsifying
subcubes {x_i1=x_i2=x_i3=0}, rho=3) and (b) random rho=1,2 subcubes.   usage: kt_cd.py p"""
import sys, random
from kt_deg import php
from pcdeg import *
from r3lib import *
from r3_e2 import greedy, rand_subcube
from r3_e3 import closureS, CD_function_rows
p = int(sys.argv[1]); n, ax = php(4, 3, p)
h, S, sp = closureS(n, ax, 3, p); assert not h
cube = Cube(n, p); Q0 = Quot(cube, None); Q = Quot(cube, CD_function_rows(cube, S, sp))
print(f"PHP4->3 p={p}: dim C_3 = {Q.dim} (of {cube.NK(3)} multilinear polys of degree <=3)", flush=True)
blk = [cube.indicator([([1 if j == 3 * i + b else 0 for j in range(n)], 0) for b in range(3)]) for i in range(4)]
rnd = random.Random(2)
fams = {'pigeon blocks rho=3 s=4': (3, blk)}
for rho in (1, 2): fams[f'random subcubes rho={rho} s=6'] = (rho, [cube.indicator(rand_subcube(cube, rho, rnd)) for _ in range(6)])
for name, (rho, gs) in fams.items():
    for K in (1, 2, 3, 4):
        if p == 2 and K > 4: continue
        c0 = greedy(cube, Q0, K, gs, random.Random(1), ncomb=20, maxr=8)
        cC = greedy(cube, Q, K, gs, random.Random(1), ncomb=20, maxr=8)
        print(f" {name} K={K}: no C_D c={c0}   mod C_3 c={cC}", flush=True)
