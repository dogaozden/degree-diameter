"""For a k-regular bipartite controller and walk length L (= D - 1), count the target pairs (u, v) at the right parity
(same side if L even, opposite if odd) that are joined by a nonbacktracking walk of length exactly L, by distance.
Pairs joined by such a walk are covered by any chart that is universal at the top distance; the others need the
chart's detour coverage.  usage: python3 nbwalk_cover.py EDGES L"""
import sys
from collections import deque, Counter
from controller import read_graph
n, E = read_graph(sys.argv[1]); L = int(sys.argv[2])
adj = [[] for _ in range(n)]
for u, v in E: adj[u].append(v); adj[v].append(u)
side = [-1] * n; side[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if side[y] < 0: side[y] = 1 - side[x]; dq.append(y)
girth = min((lambda s: (lambda d, par: next((d[x] + d[y] + 1 for x in range(n) for y in adj[x] if d[x] >= 0 and d[y] >= 0 and par[x] != y and par[y] != x and x < y), 10**9))(*bfs(s)))(s) for s in range(min(n, 50))) if False else None
def bfsdist(s):
    d = [-1] * n; d[s] = 0; dq = deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
tot = Counter(); hit = Counter(); srcs = range(0, n, max(1, n // 60))
for s in srcs:
    d = bfsdist(s)
    # NB walks of length L from s: states (vertex, previous vertex)
    cur = {(y, s) for y in adj[s]}
    for _ in range(L - 1):
        cur = {(z, y) for (y, x) in cur for z in adj[y] if z != x}
    ends = {y for (y, x) in cur}
    for v in range(n):
        if (side[v] == side[s]) == (L % 2 == 0):
            tot[d[v]] += 1; hit[d[v]] += v in ends
print('controller', sys.argv[1], 'n =', n, 'walk length', L, 'sources sampled', len(srcs))
for dd in sorted(tot): print('  distance %d: %d pairs, %d joined by a nonbacktracking %d-walk (%.1f%%)' % (dd, tot[dd], hit[dd], L, 100.0 * hit[dd] / tot[dd]))
