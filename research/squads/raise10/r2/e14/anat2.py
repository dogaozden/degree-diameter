#!/usr/bin/env python3
"""anat2.py SOL: per-j-fiber reach statistics for metacyclic Haar states G = Z_m x|_r Z_k (n=1).
Quotient map G -> Z_k, (a,j) -> j, is a homomorphism. For each side and each j-value c, prints the number of
elements of the fiber {(a,c)} NOT reached within D (holes), and the number of distinct reached elements per fiber
at radius D-1 and D. Also prints the order of j in Z_k and the alternating j-sum multiplicity."""
import sys, re
import numpy as np
from math import gcd
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/r2/e14')
from anatlib import parse, Gp, reach
d, D, m, k, r, S = parse(sys.argv[1])
Gr = Gp(m, k, r); N = Gr.N
print(f"Z_{m} x|_{r} Z_{k} N={N} d={d} D={D} S={S}")
for side, nm in ((0, 'A'), (1, 'B')):
    lev = reach(Gr, S, side, D)          # dist array, -1 if unreached
    for rad in (D - 1, D):
        ok = (lev >= 0) & (lev <= rad)
        jj = np.arange(N) % k
        cnt = np.bincount(jj[ok], minlength=k)
        print(f"side {nm} radius<= {rad}: reached per j-fiber (fiber size {m}); min={cnt.min()} at j={list(np.nonzero(cnt==cnt.min())[0])}")
    unr = np.nonzero(lev < 0)[0]
    print(f"side {nm}: unreached at D={D}: {len(unr)}")
    for h in unr:
        a, j = divmod(int(h), k)
        print(f"   hole side {nm}: a={a} j={j} ord_k(j)={k//gcd(j,k) if j else 1}")
