#!/usr/bin/env python3
"""c1/generic_test2.py: alpha = 3 (degree-4 base, copy degree 6 = 2*alpha) on small 4-regular bipartite bases.
Bases: K44 (D1=2) and circulant bipartite B(8; {0,1,2,3}) (D1 computed). Thesis claim: D <= D1 + 2."""
import sys, itertools
import numpy as np
from generic_test import build_generic, diameter

def base_K44():
    n = 4
    return n, np.array([(i, n + j) for i in range(n) for j in range(n)], dtype=np.int64)

def base_circ(n, S):
    return n, np.array([(i, n + (i + s) % n) for i in range(n) for s in S], dtype=np.int64)

tests = [('K44', base_K44())] + [('circ8_0123', base_circ(8, [0, 1, 2, 3]))]
for name, (n, base) in tests:
    # D1 of the base graph
    import scipy.sparse as sp
    from scipy.sparse.csgraph import shortest_path
    a, b = base[:, 0], base[:, 1]
    A = sp.coo_matrix((np.ones(2*len(a)), (np.r_[a, b], np.r_[b, a])), shape=(2*n, 2*n)).tocsr()
    D1 = int(shortest_path(A, method='D', directed=False, unweighted=True).max())
    for pat in [''.join(p) for p in itertools.product('ab', repeat=3)]:
        for side in ['P']:
            for maps in ['id', 'rand']:
                N, E = build_generic(n, base, pat, side, maps)
                d, conn = diameter(N, E)
                print(f"base {name} (D1={D1}, Delta1=4) alpha=3 pattern={pat} side={side} maps={maps}: N={N} connected={conn} diameter={int(d)} D1+2={D1+2}", flush=True)
