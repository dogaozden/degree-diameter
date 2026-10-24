# coverage of line-side hubs in the base graph (given edge file), for the super-hub set-cover question
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
def pid(p, i): return i*2*N + p
def lid(l, i): return i*2*N + N + l
hubL = [6*N + j for j in range(K)]
hubP = [6*N + K + j for j in range(K)]
res = {}
for j in range(K):
    d = bfs(hubL[j])
    cov = [set(p for p in range(N) if d[pid(p,i)] <= 6) for i in range(3)]
    hubsP = [k for k in range(K) if d[hubP[k]] <= 6]
    res[j] = (cov, hubsP)
    print("line-hub", j, "points within 6 per level:", [len(c) for c in cov], "point-hubs within 6:", hubsP, flush=True)
# greedy / exhaustive: smallest D (|D|<=7) covering all points at all 3 levels
universe = [(p,i) for p in range(N) for i in range(3)]
best = None
for size in range(4, 8):
    found = None
    for D in itertools.combinations(range(K), size):
        ok = True
        for i in range(3):
            u = set()
            for j in D: u |= res[j][0][i]
            if len(u) < N: ok = False; break
        if ok:
            found = D; break
    print("size", size, "cover of all points on 3 levels:", found, flush=True)
    if found: break
