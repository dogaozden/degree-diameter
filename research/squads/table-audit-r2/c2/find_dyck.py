# Random 32-vertex cubic bipartite girth-6 graph (Dyck-graph substitute: same order/degree/bipartite/girth 6). Writes bases/dyck.txt
import random
from collections import deque
n = 16  # per side; vertices 0..15 left, 16..31 right
def girth(adj):
    g = 10**9
    for s in range(32):
        d = [-1]*32; par = [-1]*32; d[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x]+1; par[y] = x; q.append(y)
                elif par[x] != y: g = min(g, d[x]+d[y]+1)
    return g
random.seed(7)
for trial in range(2000000):
    # union of three perfect matchings between left and right, rejecting multi-edges
    edges = set(); ok = True
    for _ in range(3):
        perm = list(range(16)); random.shuffle(perm)
        for i in range(16):
            e = (i, 16 + perm[i])
            if e in edges: ok = False; break
            edges.add(e)
        if not ok: break
    if not ok: continue
    adj = [[] for _ in range(32)]
    for u, w in edges: adj[u].append(w); adj[w].append(u)
    if girth(adj) == 6:
        break
else:
    raise SystemExit("not found")
print("trial", trial, "girth", girth(adj))
with open("bases/dyck.txt", "w") as f:
    f.write(f"32 {len(edges)}\n")
    for u, w in sorted(edges): f.write(f"{u} {w}\n")
