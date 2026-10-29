#!/usr/bin/env python3
"""The (5,5) graph on 360 vertices from its voltages in Z15 x S3 alone (no GAP table): lift of the base
[[2,3],[3,2]] (A0, A1 | B0, B1). An edge a -> b of voltage g joins (a, h) and (b, h g). Elements are (t, p) with t in
Z15 and p a permutation of {1,2,3}; products are (t, p)(s, q) = (t + s, p q) with GAP's convention i^(p q) = (i^p)^q.
Writes the edge list (first line = number of vertices) and checks degree, bipartiteness and diameter by BFS.
usage: build_d5D5_n360_z15s3.py [OUT.edges]"""
import sys
from collections import deque
from itertools import permutations
I, T13, T23 = (1, 2, 3), (3, 2, 1), (1, 3, 2)          # images of 1, 2, 3
S3 = list(permutations((1, 2, 3)))
def pm(p, q): return tuple(q[p[i] - 1] for i in range(3))   # i -> q(p(i))
G = [(t, p) for t in range(15) for p in S3]; idx = {g: k for k, g in enumerate(G)}; m = len(G)
def mul(a, b): return ((a[0] + b[0]) % 15, pm(a[1], b[1]))
volt = {(0, 2): [(0, I), (6, T13)], (0, 3): [(0, I), (10, T13), (12, T23)],
        (1, 2): [(0, T13), (1, T23), (9, T23)], (1, 3): [(0, I), (6, T13)]}
E = set()
for (a, b), gs in volt.items():
    for g in gs:
        for h in G:
            e = (a * m + idx[h], b * m + idx[mul(h, g)]); assert e not in E; E.add(e)
n = 4 * m; adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
assert all(len(x) == 5 for x in adj)
diam = 0
for s in range(n):
    d = [-1] * n; d[s] = 0; q = deque([s])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if d[v] < 0: d[v] = d[u] + 1; q.append(v)
            else: assert (d[v] - d[u]) % 2 == 1    # bipartite
    assert min(d) >= 0; diam = max(diam, max(d))
print(f"n={n} edges={len(E)} 5-regular bipartite diameter={diam}", "VALID (5,5)" if diam == 5 else "NOT VALID")
if len(sys.argv) > 1:
    with open(sys.argv[1], 'w') as o:
        o.write(f"{n}\n"); [o.write(f"{u} {v}\n") for u, v in sorted(E)]
