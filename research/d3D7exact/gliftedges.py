#!/usr/bin/env python3
"""Edge list of a glift solution. Usage: gliftedges.py GROUPFILE BASES "SOL line" > out.edges
Lift vertex (x, g) = x*N + g; base edge (a, b) (a on side 0 of the BFS 2-colouring from vertex 0) with voltage h
gives (a, g) ~ (b, g*h)."""
import sys
gfile, bases, sol = sys.argv[1], sys.argv[2], sys.argv[3].split()
bid, gid, volt = int(sol[1]), int(sol[2]), list(map(int, sol[4:]))
toks = open(gfile).read().split(); i = 0; grp = None
while i < len(toks):
    if toks[i] == 'G':
        N, g = int(toks[i + 1]), int(toks[i + 2]); i += 4
        mul = [list(map(int, toks[i + r * N:i + (r + 1) * N])) for r in range(N)]; i += N * N
        if g == gid: grp = (N, mul)
    elif toks[i] == 'A': i += 2 + int(toks[i + 1])
    else: i += 1
N, mul = grp
b = [l.split() for l in open(bases) if l.strip()][bid]
nv, ns = int(b[0]), int(b[1]); E = []
for j in range(ns):
    a, c, m = map(int, b[2 + 3 * j:5 + 3 * j]); E += [(a, c)] * m
adj = {x: [] for x in range(nv)}
for a, c in E: adj[a].append(c); adj[c].append(a)
side = {0: 0}; q = [0]
for x in q:
    for y in adj[x]:
        if y not in side: side[y] = 1 - side[x]; q.append(y)
print(nv * N)
for (a, c), h in zip(E, volt):
    if side[a] == 1: a, c = c, a
    for g in range(N): print(a * N + g, c * N + mul[g][h])
