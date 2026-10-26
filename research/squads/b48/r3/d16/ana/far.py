import sys, collections
from collections import deque
edges_file = sys.argv[1]; D = int(sys.argv[2]) if len(sys.argv) > 2 else 9
lines = open(edges_file).read().split("\n")
n = int(lines[0]); adj = [[] for _ in range(n)]
for l in lines[1:]:
    if l.strip():
        u, v = map(int, l.split()); adj[u].append(v); adj[v].append(u)
N = n // 2; m, k = 104, 24
def bfs(src):
    dist = [-1]*n; dist[src] = 0; q = deque([src])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x]+1; q.append(y)
    return dist
for src, name in ((0, "A"), (N, "B")):
    d = bfs(src)
    far = [x for x in range(n) if d[x] > D or d[x] < 0]
    print("from", name, "far:", len(far))
    for x in far:
        side = "A" if x < N else "B"; y = x % N
        print("  ", side, "a=%d j=%d" % (y % m, y // m), "dist", d[x])
