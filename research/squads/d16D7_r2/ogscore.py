#!/usr/bin/env python3
"""ogscore.py GRAPH SOL: checks that SOL (one orbit-graph index per line, '#' lines ignored) is an independent set of
the orbit graph GRAPH (og_pts.txt or og_lines.txt: "M E", then per vertex "idx rep deg nbrs...").
Prints "VALID orbits=K elements=61K" or "INVALID <reason>". Exit code 0 iff valid."""
import sys
g, s = sys.argv[1], sys.argv[2]
with open(g) as f:
    M, E = map(int, f.readline().split())
    nb = [None] * M
    for line in f:
        a = list(map(int, line.split()))
        nb[a[0]] = set(a[3:3 + a[2]])
sol = []
for line in open(s):
    line = line.strip()
    if line and not line.startswith('#'):
        sol.append(int(line))
S = set(sol)
if len(S) != len(sol):
    print('INVALID duplicate'); sys.exit(1)
for v in sol:
    if not 0 <= v < M:
        print('INVALID index', v); sys.exit(1)
    if nb[v] & S:
        print('INVALID edge', v, min(nb[v] & S)); sys.exit(1)
print('VALID orbits=%d elements=%d' % (len(sol), 61 * len(sol)))
