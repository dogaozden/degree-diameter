import sys
from collections import deque
edges, D, b, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
L = open(edges).read().split(); N = int(L[0]); adj = [[] for _ in range(N)]
for i in range(1, len(L), 2):
    x, y = int(L[i]), int(L[i+1]); adj[x].append(y); adj[y].append(x)
tot = 0
for u in range(b):
    s = u * n; dist = [-1]*N; dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
    tot += sum(1 for v in range(N) if dist[v] > D or dist[v] < 0)
print("cost", tot, "ordered pairs total (all sources)", tot * n)
