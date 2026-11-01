#!/usr/bin/env python3
"""Build the bipartite route-chart lift of a Haar controller H(G,S) (|S| = 4) with a chart over F_4^4, as an edge list
for apsp.c.  Vertex (g, x)_A -> index g*256 + vid(x); (h, y)_B -> |G|*256 + h*256 + vid(y).
Edge (g, x)_A -- (s_i g, A_i x + lam b_i)_B for lam in F_4.
usage: python3 build_lift.py "<group spec>" "s0 s1 s2 s3" chart.json out.edges"""
import sys, json, itertools
import numpy as np
import controller as ct
from chart import mat_vec, MUL, vid

spec, Sstr, chartfile, out = sys.argv[1:5]
T = ct.parse(spec); G = ct.Group(T); m = G.m
S = list(map(int, Sstr.split()))
ch = json.load(open(chartfile)); A = ch['A']; b = [tuple(v) for v in ch['b']]
vecs = list(itertools.product(range(4), repeat=4))
nA = m * 256
edges = []
for g in range(m):
    for x in vecs:
        u = g * 256 + vid(x)
        for i in range(4):
            h = int(T[S[i], g]); y0 = mat_vec(A[i], x)
            for lam in range(4):
                y = tuple(a ^ MUL[lam][c] for a, c in zip(y0, b[i]))
                edges.append((u, nA + h * 256 + vid(y)))
assert len(set(edges)) == len(edges), "repeated edge"
with open(out, 'w') as f:
    f.write(f"{2 * nA}\n")
    f.writelines(f"{a} {c}\n" for a, c in edges)
print('vertices', 2 * nA, 'edges', len(edges))
