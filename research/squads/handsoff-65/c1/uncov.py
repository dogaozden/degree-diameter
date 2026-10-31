# usage: uncov.py EDGES : BFS from each base vertex's identity fibre; list unreached lift vertices (distance > 5)
import sys
from collections import deque
with open(sys.argv[1]) as f:
    n = int(f.readline()); adj = [[] for _ in range(n)]
    for line in f:
        p = line.split()
        if len(p) < 2: continue
        u, v = int(p[0]), int(p[1]); adj[u].append(v); adj[v].append(u)
m = n // 4
for s in [0, m, 2*m, 3*m]:
    dist = [-1]*n; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x]+1; q.append(y)
    far = [v for v in range(n) if dist[v] < 0 or dist[v] > 5]
    print("source", s, "far", len(far), [(v//m, v % m) for v in far][:8])
