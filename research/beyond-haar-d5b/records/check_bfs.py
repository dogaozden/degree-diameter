#!/usr/bin/env python3
"""Independent check of an edge list (first line n, then "u v" per edge): simple, regular of degree d, bipartite,
connected, and the exact diameter by a BFS from every vertex (plain Python, no symmetry assumed).
usage: check_bfs.py EDGES d D   -> prints VALID if the graph is d-regular, bipartite and of diameter exactly D"""
import sys
from collections import deque
lines = open(sys.argv[1]).read().split('\n')
n = int(lines[0]); d, D = int(sys.argv[2]), int(sys.argv[3])
adj = [set() for _ in range(n)]; ne = 0
for ln in lines[1:]:
    t = ln.split()
    if len(t) < 2: continue
    u, v = int(t[0]), int(t[1])
    assert u != v and v not in adj[u], "loop or repeated edge"
    adj[u].add(v); adj[v].add(u); ne += 1
degs = set(len(a) for a in adj)
col = [-1] * n; col[0] = 0; q = deque([0]); bip = True
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
        elif col[y] == col[x]: bip = False
conn = all(c >= 0 for c in col)
diam = 0
for s in range(n):
    dist = [-1] * n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
    if min(dist) < 0: diam = -1; break
    diam = max(diam, max(dist))
ok = degs == {d} and bip and conn and diam == D
print(f"n={n} edges={ne} degrees={sorted(degs)} bipartite={bip} connected={conn} diameter={diam} -> {'VALID' if ok else 'INVALID'}")
