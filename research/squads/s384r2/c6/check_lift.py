#!/usr/bin/env python3
"""Independent check: build the explicit Z3 lift from a voltage file and BFS from every
fiber representative (u,0). Prints the number of lift vertices at distance > 5 (summed over
the 312 sources u), the lift diameter, and the apsp-style check numbers.

usage: check_lift.py voltages.txt
voltages.txt: first line = cost, then lines 'a b voltage istree' for each base edge.
"""
import sys
from collections import deque

path = sys.argv[1]
lines = open(path).read().split("\n")
edges = []
for ln in lines[1:]:
    if ln.strip():
        a, b, v, _ = map(int, ln.split())
        edges.append((a, b, v))
NB = 312
M = 3
# lift vertex id = w*3 + h
adj = [[] for _ in range(NB * M)]
for a, b, v in edges:
    for g in range(M):
        x = a * M + g
        y = b * M + (g + v) % M
        adj[x].append(y)
        adj[y].append(x)
assert all(len(adj[x]) == 6 for x in range(NB * M))


def bfs(s):
    d = [-1] * (NB * M)
    d[s] = 0
    dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                dq.append(y)
    return d


total_far = 0
diam = 0
unconn = 0
for u in range(NB):
    d = bfs(u * M)
    if min(d) < 0:
        unconn += 1
        continue
    diam = max(diam, max(d))
    total_far += sum(1 for x in d if x > 5)
print(f"lift vertices=936 disconnected_sources={unconn} lift_eccentricity_max_over_sources={diam}")
print(f"sum over sources (u,0) of #lift vertices at distance > 5 = {total_far}")
print("VALID_D5" if total_far == 0 else "NOT_D5")
