import sys
from collections import deque
def load(p):
    with open(p) as f:
        n = int(f.readline()); M = [list(map(int, f.readline().split())) for _ in range(n)]
    return n, M
n, M = load(sys.argv[1]); S = list(map(int, sys.argv[2].split(",")))
NV = 2*n
adj = [[] for _ in range(NV)]
for x in range(n):
    for s in S:
        y = M[s][x]; adj[x].append(n+y); adj[n+y].append(x)
bad = 0; maxd = 0
for v in range(NV):
    dist = [-1]*NV; dist[v] = 0; q = deque([v])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u]+1; q.append(w)
    side = range(n) if v < n else range(n, NV)
    for w in side:
        if dist[w] < 0 or dist[w] > 4: bad += 1
    maxd = max(maxd, max(dist))
print("ordered same-side pairs with dist>4 or unreachable:", bad, "max dist", maxd, "deg", set(len(a) for a in adj))
