#!/usr/bin/env python3
"""Build the incidence graph of GQ(5,5) = W(5) (symplectic quadrangle) and check it.

Points: 156 projective points of PG(3,5), normalised (first nonzero coordinate = 1).
Lines: totally isotropic lines of the form B(x,y)=x1y2-x2y1+x3y4-x4y3 over GF(5).
Vertices 0..155 are points, 156..311 are lines. Writes edges to gq55_edges.txt.
"""
import itertools
import sys
from collections import deque

Q = 5


def normalise(v):
    for c in v:
        if c % Q:
            inv = pow(c, Q - 2, Q)
            return tuple((x * inv) % Q for x in v)
    return None


def form(x, y):
    return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % Q


points = sorted({normalise(v) for v in itertools.product(range(Q), repeat=4) if any(v)})
assert len(points) == 156, len(points)
pidx = {p: i for i, p in enumerate(points)}

lines = set()
for i, p in enumerate(points):
    for j in range(i + 1, len(points)):
        q = points[j]
        if form(p, q) == 0:
            span = set()
            for a, b in itertools.product(range(Q), repeat=2):
                if a or b:
                    v = tuple((a * p[k] + b * q[k]) % Q for k in range(4))
                    span.add(pidx[normalise(v)])
            lines.add(frozenset(span))
lines = sorted(lines, key=lambda s: sorted(s))
assert len(lines) == 156, len(lines)
assert all(len(L) == 6 for L in lines)

n = 156 + len(lines)
adj = [[] for _ in range(n)]
for li, L in enumerate(lines):
    for p in L:
        adj[p].append(156 + li)
        adj[156 + li].append(p)
for v in range(n):
    adj[v].sort()
assert all(len(a) == 6 for a in adj), "not 6-regular"


def bfs(s):
    d = [-1] * n
    d[s] = 0
    dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                dq.append(y)
    return d


diam = 0
girth = 10**9
for s in range(n):
    d = bfs(s)
    assert min(d) >= 0, "disconnected"
    diam = max(diam, max(d))
# girth: shortest cycle through BFS from each vertex
for s in range(n):
    d = [-1] * n
    par = [-1] * n
    d[s] = 0
    dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                par[y] = x
                dq.append(y)
            elif par[x] != y:
                girth = min(girth, d[x] + d[y] + 1)
assert all(len(set(x for x in adj[v])) == 6 for v in range(n))
print(f"vertices={n} degree=6 bipartite=yes diameter={diam} girth={girth}")
assert n == 312 and diam == 4 and girth == 8

with open("/home/user/degree-diameter/research/squads/s384r2/c6/gq55_edges.txt", "w") as f:
    edges = [(v, w) for v in range(n) for w in adj[v] if v < w]
    f.write(f"{n} {len(edges)}\n")
    for v, w in edges:
        f.write(f"{v} {w}\n")
print("edges", len(edges))
