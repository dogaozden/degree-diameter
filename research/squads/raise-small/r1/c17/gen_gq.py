#!/usr/bin/env python3
"""Incidence graph of GQ(3,3) = W(3): points of PG(3,3) (40), totally isotropic lines of the symplectic form (40).
Writes gq33.base: first line "nb ne", then "p l" with p in 0..39 (points) and l in 40..79 (lines).
Checks 4-regular, girth 8, diameter 4."""
import itertools
from collections import deque
q = 3
def B(x, y):  # symplectic form x1y2-x2y1+x3y4-x4y3 mod 3
    return (x[0]*y[1]-x[1]*y[0]+x[2]*y[3]-x[3]*y[2]) % q
vecs = [v for v in itertools.product(range(q), repeat=4) if any(v)]
def norm(v):
    for c in v:
        if c:
            inv = 1 if c == 1 else 2
            return tuple((inv*x) % q for x in v)
pts = sorted({norm(v) for v in vecs})
assert len(pts) == 40
# totally isotropic lines: pairs of orthogonal points span a totally isotropic line
lines = set()
for a, b in itertools.combinations(pts, 2):
    if B(a, b) == 0:
        span = set()
        for s, t in itertools.product(range(q), repeat=2):
            v = tuple((s*a[i]+t*b[i]) % q for i in range(4))
            if any(v):
                span.add(norm(v))
        if len(span) == 4:
            lines.add(frozenset(span))
lines = sorted(sorted(L) for L in lines)
assert len(lines) == 40, len(lines)
P = {p: i for i, p in enumerate(pts)}
edges = []
for j, L in enumerate(lines):
    for p in L:
        edges.append((P[p], 40 + j))
n = 80
adj = [[] for _ in range(n)]
for u, v in edges:
    adj[u].append(v); adj[v].append(u)
assert all(len(a) == 4 for a in adj)
def bfs(s):
    d = [-1]*n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x]+1; dq.append(y)
    return d
diam = max(max(bfs(s)) for s in range(n))
girth = min(min(bfs(s)[u] for u in [0]) for s in [0]) if False else None
# girth: shortest cycle via BFS from each vertex
g = 10**9
for s in range(n):
    d = [-1]*n; par = [-1]*n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x]+1; par[y] = x; dq.append(y)
            elif par[x] != y:
                g = min(g, d[x]+d[y]+1)
print("vertices", n, "edges", len(edges), "diameter", diam, "girth", g)
with open("gq33.base", "w") as f:
    f.write(f"{n} {len(edges)}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
