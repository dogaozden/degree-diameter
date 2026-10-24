"""Incidence graph of PG(2,9) as a base graph for voltage lifts (card c7).

GF(9) = GF(3)[i]/(i^2+1); element e = a + 3b stands for a + b*i.
Points 0..90 (normalized projective points), lines 91..181 (same normalized triples as line coordinates).
Writes base file: first line "NB E", then one line "u v tree" per edge, u = point, v = line,
tree = 1 for edges of a BFS spanning tree from vertex 0 (their voltages are fixed to 0; WLOG for abelian lifts).
Checks: 10-regular, simple, diameter 3, girth 6 (two points share exactly one line).
usage: python3 build_base.py OUT
"""
import sys
from collections import deque

def add(e, f):
    return (e % 3 + f % 3) % 3 + 3 * (((e // 3) + (f // 3)) % 3)

def mul(e, f):
    a, b, c, d = e % 3, e // 3, f % 3, f // 3
    return ((a * c - b * d) % 3) + 3 * ((a * d + b * c) % 3)

def neg(e):
    return ((-(e % 3)) % 3) + 3 * ((-(e // 3)) % 3)

INV = {e: next(f for f in range(1, 9) if mul(e, f) == 1) for e in range(1, 9)}

def normalize(v):
    for c in v:
        if c:
            ic = INV[c]
            return tuple(mul(ic, x) for x in v)
    return None

pts = sorted({normalize(v) for v in __import__('itertools').product(range(9), repeat=3) if any(v)})
assert len(pts) == 91, len(pts)
lines = pts  # line [a,b,c]: a x + b y + c z = 0

def dot(l, p):
    s = 0
    for x, y in zip(l, p):
        s = add(s, mul(x, y))
    return s

NP = len(pts)
edges = []  # (point, line)
for pi, p in enumerate(pts):
    for li, l in enumerate(lines):
        if dot(l, p) == 0:
            edges.append((pi, li))
assert len(edges) == 910, len(edges)
deg = [0] * (2 * NP)
for p, l in edges:
    deg[p] += 1
    deg[NP + l] += 1
assert all(d == 10 for d in deg), set(deg)

# shared lines: two distinct points lie on exactly one common line (girth 6)
on = [set() for _ in range(NP)]
for p, l in edges:
    on[p].add(l)
for p in range(NP):
    for q in range(p + 1, NP):
        assert len(on[p] & on[q]) == 1

# base-graph adjacency and diameter
V = 2 * NP
adj = [[] for _ in range(V)]
E = []
for p, l in edges:
    u, v = p, NP + l
    adj[u].append(v)
    adj[v].append(u)
    E.append((u, v))

def bfs(s):
    d = [-1] * V
    d[s] = 0
    q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                q.append(y)
    return d

diam = max(max(bfs(s)) for s in range(V))
assert diam == 3, diam

# BFS spanning tree from vertex 0
par = [-1] * V
seen = [False] * V
seen[0] = True
q = deque([0])
tree = set()
while q:
    x = q.popleft()
    for y in adj[x]:
        if not seen[y]:
            seen[y] = True
            tree.add((min(x, y), max(x, y)))
            q.append(y)
assert len(tree) == V - 1

with open(sys.argv[1], 'w') as f:
    f.write(f"{V} {len(E)}\n")
    for u, v in E:
        f.write(f"{u} {v} {1 if (min(u, v), max(u, v)) in tree else 0}\n")
print("base PG(2,9) incidence: V=%d E=%d deg=10 diameter=%d girth>=6 OK, tree edges=%d" % (V, len(E), diam, len(tree)))
