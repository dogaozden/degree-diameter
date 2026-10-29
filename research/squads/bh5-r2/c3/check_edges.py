# independent check: degrees, bipartiteness, and BFS distance profile from vertex 0 and from the right base vertex
import sys
from collections import deque
lines = open(sys.argv[1]).read().split("\n")
V = int(lines[0]); adj = [[] for _ in range(V)]
for ln in lines[1:]:
    if ln.strip():
        u, w = map(int, ln.split()); adj[u].append(w); adj[w].append(u)
degs = set(len(a) for a in adj)
half = V // 2
bip = all((u < half) != (w < half) for u in range(V) for w in adj[u])
def bfs(s):
    d = [-1] * V; d[s] = 0; q = deque([s])
    while q:
        v = q.popleft()
        for w in adj[v]:
            if d[w] < 0: d[w] = d[v] + 1; q.append(w)
    return d
unreached = 0; ecc = []
for s in (0, half):
    d = bfs(s)
    unreached += sum(1 for x in d if x < 0 or x > 5)
    ecc.append(max(d))
print("V", V, "degrees", degs, "bipartite", bip, "cost(independent)", unreached, "ecc", ecc)
