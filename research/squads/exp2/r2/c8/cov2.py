# best union of line-hub reach sets (points, per level) for |D| = 7, exhaustive over 7-subsets
import sys, itertools
from collections import deque
edges_file = sys.argv[1]; N = 3906; K = 13
with open(edges_file) as f:
    n = int(f.readline())
    adj = [[] for _ in range(n)]
    for line in f:
        a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
def bfs(s):
    d = [-1]*n; d[s] = 0; dq = deque([s])
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if d[w] < 0: d[w] = d[v]+1; dq.append(w)
    return d
hubL = [6*N + j for j in range(K)]
masks = []   # bitmask over (level, point): bit i*N+p
for j in range(K):
    d = bfs(hubL[j]); m = 0
    for i in range(3):
        for p in range(N):
            if d[i*2*N + p] <= 6: m |= 1 << (i*N + p)
    masks.append(m)
full = (1 << (3*N)) - 1
best = (-1, None)
for size in (7,):
    for D in itertools.combinations(range(K), size):
        u = 0
        for j in D: u |= masks[j]
        c = [bin(u >> (i*N) & ((1<<N)-1)).count('1') for i in range(3)]
        if min(c) > best[0]: best = (min(c), D, c)
print("best %d-set (min over levels) =" % size, best, "of", N, flush=True)
# union over all 13 hubs
u = 0
for j in range(K): u |= masks[j]
print("union over all 13 line-hubs per level:", [bin(u >> (i*N) & ((1<<N)-1)).count('1') for i in range(3)])
