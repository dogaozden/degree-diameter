"""hubbfs.py EDGES NHUBSTART: BFS from every hub vertex (ids >= NHUBSTART) and from (v,0) sources is NOT done here;
prints the number of (hub, target) pairs at distance > 5 and the max distance from hubs. Independent of dmhub.c."""
import sys
from collections import deque
with open(sys.argv[1]) as f:
    n = int(f.readline()); adj = [[] for _ in range(n)]
    for ln in f:
        a, b = map(int, ln.split()); adj[a].append(b); adj[b].append(a)
h0 = int(sys.argv[2]); bad = 0; mx = 0
degs = sorted(set(len(a) for a in adj))
for s in range(h0, n):
    d = [-1] * n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    bad += sum(1 for t in range(n) if d[t] < 0 or d[t] > 5); mx = max(mx, max(d))
print('n', n, 'degrees', degs, 'hub sources', n - h0, 'pairs at distance > 5 from hubs', bad, 'max hub eccentricity', mx)
