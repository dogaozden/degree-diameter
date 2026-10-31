import sys
from collections import deque
# usage: viol.py EDGES : per-vertex count of vertices at distance > 5 for vertex orbit representatives (vertex 0 and
# the first vertex of each degree class). Prints the count of far vertices from each of the first 8 vertices.
f = open(sys.argv[1]).read().split()
n = int(f[0]); adj = [[] for _ in range(n)]
for i in range(1, len(f), 2):
    u, v = int(f[i]), int(f[i+1]); adj[u].append(v); adj[v].append(u)
def far(s):
    d = [-1]*n; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x]+1; q.append(y)
    return sum(1 for x in range(n) if d[x] > 5 or d[x] < 0)
print([far(s) for s in range(0, n, max(1, n//8))][:8])
