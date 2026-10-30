#!/usr/bin/env python3
"""Independent check (plain Python, no shared code with apsp.c): simple graph, max degree, bipartite, connected,
exact diameter by BFS from every vertex.  usage: check_independent.py EDGES DELTA D"""
import sys
from collections import deque
path, delta, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
lines = [l for l in open(path) if l.strip()]
n = int(lines[0]); adj = [set() for _ in range(n)]; m = 0
for l in lines[1:]:
    a, b = map(int, l.split()[:2])
    assert a != b and 0 <= a < n and 0 <= b < n, "bad edge"
    assert b not in adj[a], "repeated edge"
    adj[a].add(b); adj[b].add(a); m += 1
col = [-1] * n; col[0] = 0; q = deque([0]); bip = True
while q:
    x = q.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
        elif col[y] == col[x]: bip = False
assert all(c >= 0 for c in col), "disconnected"
diam = 0
for s in range(n):
    dist = [-1] * n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
    diam = max(diam, max(dist))
maxdeg = max(len(a) for a in adj)
print(f"n={n} edges={m} maxdeg={maxdeg} mindeg={min(len(a) for a in adj)} bipartite={bip} diameter={diam} sides={col.count(0)}+{col.count(1)}")
print("VALID" if bip and maxdeg <= delta and diam <= D else "INVALID", f"(Delta={delta}, D={D})")
