#!/usr/bin/env python3
"""Edge list of a Z_p lift found by zplift.
Usage: liftedges.py BASES BASEID P "v0 v1 ..." > out.edges
BASES is the multig -T file given to zplift; voltages are for the expanded edge list (multiplicities expanded, in file
order); each edge is oriented from side 0 (BFS 2-colouring from vertex 0) to side 1, as in zplift.
Lift vertex (x, g) = x*P + g; edge (a, b) with voltage t gives (a, g) ~ (b, g + t)."""
import sys
bases, bid, p, volt = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), list(map(int, sys.argv[4].split()))
line = [l for l in open(bases) if l.strip()][bid].split()
nv, ns = int(line[0]), int(line[1])
E = []
for i in range(ns):
    a, b, m = map(int, line[2 + 3 * i: 5 + 3 * i])
    E += [(a, b)] * m
adj = {i: [] for i in range(nv)}
for a, b in E:
    adj[a].append(b); adj[b].append(a)
side = {0: 0}; q = [0]
for x in q:
    for y in adj[x]:
        if y not in side:
            side[y] = 1 - side[x]; q.append(y)
assert len(volt) == len(E)
print(nv * p)
for (a, b), t in zip(E, volt):
    if side[a] == 1:
        a, b = b, a
    for g in range(p):
        print(a * p + g, b * p + (g + t) % p)
