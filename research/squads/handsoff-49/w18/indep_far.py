# indep_far.py EDGES D : independent check (pure Python, no shared code with tools/): BFS from every vertex.
# Prints n, edges, degree range, bipartite flag, connectivity, diameter, count of unordered pairs at distance > D.
import sys
from collections import deque
path, D = sys.argv[1], int(sys.argv[2])
with open(path) as f:
    toks = f.read().split()
n = int(toks[0]); vals = list(map(int, toks[1:]))
adj = [[] for _ in range(n)]
seen = set()
bad = 0
for i in range(0, len(vals) - 1, 2):
    u, v = vals[i], vals[i + 1]
    if u == v or not (0 <= u < n and 0 <= v < n):
        bad += 1; continue
    key = (min(u, v), max(u, v))
    if key in seen:
        bad += 1; continue
    seen.add(key)
    adj[u].append(v); adj[v].append(u)
deg = [len(a) for a in adj]
# bipartite check by 2-colouring
col = [-1] * n; bip = True; comps = 0
for s in range(n):
    if col[s] >= 0: continue
    comps += 1; col[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
            elif col[y] == col[x]: bip = False
far2 = 0; diam = 0; disc = False
for s in range(n):
    dist = [-1] * n; dist[s] = 0; dq = deque([s]); cnt = 0; ecc = 0
    while dq:
        x = dq.popleft(); dx = dist[x]
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dx + 1; dq.append(y)
    for y in range(n):
        d = dist[y]
        if d < 0: disc = True; far2 += 1
        else:
            if d > diam: diam = d
            if d > D: far2 += 1
print(f"n={n} edges={len(seen)} bad_edges={bad} deg={min(deg)}..{max(deg)} bipartite={bip} components={comps} "
      f"diameter={'inf' if disc else diam} far_pairs={far2 // 2}")
