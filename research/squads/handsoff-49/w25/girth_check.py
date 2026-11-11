# girth_check.py: girth and diameter of the incidence graph of H(3) (seeds/hexagon_q3.json), independent of w4/w18 code.
import json, sys
from collections import deque
d = json.load(open(sys.argv[1]))
P = d["points"]; L = d["lines"]
n = P + len(L)
adj = [[] for _ in range(n)]
for i, ln in enumerate(L):
    for p in ln:
        adj[p].append(P + i); adj[P + i].append(p)
deg = sorted(set(len(a) for a in adj))
girth = None; diam = 0
for s in range(n):
    dist = [-1] * n; par = [-1] * n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1; par[y] = x; q.append(y)
            elif par[x] != y:
                c = dist[x] + dist[y] + 1
                if girth is None or c < girth: girth = c
    diam = max(diam, max(dist))
print("n=%d degrees=%s girth=%s diameter=%d" % (n, deg, girth, diam))
