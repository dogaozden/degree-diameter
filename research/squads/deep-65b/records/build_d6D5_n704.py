#!/usr/bin/env python3
"""Build the (6,5) graph on 704 vertices (deep-65b, Nov 2 2026) from its definition alone (no group table, no GAP).

Group: G = Z11 x M16, where M16 = C8 : C2 = <x, y | x^8 = y^2 = 1, y x y^-1 = x^5> (the modular group of order 16);
G = SmallGroup(176,23) ("C11 x (C8 : C2)"). Element (a, i, j) = a x^i y^j with a in Z11, i in Z8, j in Z2, and
    (a, i, j) (b, k, l) = (a + b mod 11, i + 5^j k mod 8, j + l mod 2).
Graph: a regular voltage lift of the 2+2 base [[1,5],[5,1]] (A0-B0 one edge, A0-B1 five, A1-B0 five, A1-B1 one).
With E1, E2 below, the vertices are A0_h, A1_h, B0_h, B1_h (h in G) and the edges are
    A0_h - B0_h,   A1_h - B1_h,   A0_h - B1_{h e} (e in E1),   B0_h - A1_{h e} (e in E2),
i.e. the degree-10 Haar graph H(G, E1 u E2) with every vertex split into an edge. 6-regular, bipartite (A = A0 u A1,
B = B0 u B1), 4 x 176 = 704 vertices, 2112 edges, diameter 5.
Vertex numbering: (a, i, j) -> a*16 + i*2 + j; A0 = 0..175, A1 = 176..351, B0 = 352..527, B1 = 528..703.
usage: python3 build_d6D5_n704.py OUT.edges      (also runs its own BFS check)
"""
import sys
from collections import deque

E1 = [(7, 5, 1), (9, 7, 0), (4, 4, 1), (6, 0, 0), (1, 1, 0)]
E2 = [(7, 1, 1), (8, 0, 1), (6, 1, 0), (9, 0, 1), (5, 4, 0)]

def mul(u, v):
    a, i, j = u; b, k, l = v
    return ((a + b) % 11, (i + k * pow(5, j, 8)) % 8, (j + l) % 2)

G = [(a, i, j) for a in range(11) for i in range(8) for j in range(2)]
idx = {g: g[0] * 16 + g[1] * 2 + g[2] for g in G}
m = len(G)
A0, A1, B0, B1 = 0, m, 2 * m, 3 * m
edges = set()
for h in G:
    edges.add((A0 + idx[h], B0 + idx[h]))
    edges.add((A1 + idx[h], B1 + idx[h]))
    for e in E1: edges.add((A0 + idx[h], B1 + idx[mul(h, e)]))
    for e in E2: edges.add((A1 + idx[mul(h, e)], B0 + idx[h]))
n = 4 * m
assert len(edges) == 6 * 2 * m, "repeated edge"

adj = [[] for _ in range(n)]
for u, v in edges: adj[u].append(v); adj[v].append(u)
assert all(len(a) == 6 for a in adj), "not 6-regular"
side = lambda v: 0 if v < 2 * m else 1
assert all(side(u) != side(v) for u, v in edges), "not bipartite"
diam = 0
for s in range(n):
    d = [-1] * n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    assert min(d) >= 0, "disconnected"
    diam = max(diam, max(d))
print(f"n={n} edges={len(edges)} 6-regular bipartite diameter={diam}")
with open(sys.argv[1], "w") as f:
    f.write(f"{n}\n")
    for u, v in sorted(edges): f.write(f"{u} {v}\n")
