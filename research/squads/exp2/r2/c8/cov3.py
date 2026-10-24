# line-side super-hub question: point-hubs z'_k reach lines within 6 (per level), best 7-set and union
import sys, itertools
from collections import deque
edges_file = sys.argv[1]; N = 3906; K = 13
with open(edges_file) as f:
    n = int(f.readline()); adj = [[] for _ in range(n)]
    for line in f:
        a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
def bfs(s):
    d = [-1]*n; d[s] = 0; dq = deque([s])
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if d[w] < 0: d[w] = d[v]+1; dq.append(w)
    return d
hubP = [6*N + K + k for k in range(K)]
masks = []
for k in range(K):
    d = bfs(hubP[k]); m = 0
    for i in range(3):
        for l in range(N):
            if d[i*2*N + N + l] <= 6: m |= 1 << (i*N + l)
    masks.append(m)
print("line counts per level for point-hub 0:", [bin(masks[0] >> (i*N) & ((1<<N)-1)).count('1') for i in range(3)])
best = (-1,)
for D in itertools.combinations(range(K), 7):
    u = 0
    for k in D: u |= masks[k]
    c = min(bin(u >> (i*N) & ((1<<N)-1)).count('1') for i in range(3))
    if c > best[0]: best = (c, D)
print("best 7 point-hubs (min over levels of covered lines):", best, "of", N, flush=True)
u = 0
for k in range(K): u |= masks[k]
print("union over all 13 point-hubs per level:", [bin(u >> (i*N) & ((1<<N)-1)).count('1') for i in range(3)])
