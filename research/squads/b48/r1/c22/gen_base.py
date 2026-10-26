# Random 4-regular bipartite base multigraphs (s+s vertices, b = 2s), union of 4 random perfect matchings.
# usage: gen_base.py S SEED TRIES OUT  -> writes the best (max girth, then fewest 4-cycles) simple base found.
import sys, random
from collections import deque
s, seed, tries, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rnd = random.Random(seed)
b = 2 * s

def girth(adj):
    g = 10**9
    for src in range(b):
        dist = [-1] * b; par = [-1] * b; dist[src] = 0; q = deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1; par[v] = u; q.append(v)
                elif par[u] != v:
                    g = min(g, dist[u] + dist[v] + 1)
    return g

def count4(adj):
    c = 0
    for u in range(s):
        for w in range(u + 1, s):
            k = len(set(adj[u]) & set(adj[w]))
            c += k * (k - 1) // 2
    return c

best = None
for _ in range(tries):
    edges = set(); ok = True
    perms = []
    for k in range(4):
        p = list(range(s)); rnd.shuffle(p); perms.append(p)
    for p in perms:
        for i in range(s):
            e = (i, s + p[i])
            if e in edges: ok = False
            edges.add(e)
    if not ok: continue
    adj = [[] for _ in range(b)]
    for (u, v) in edges: adj[u].append(v); adj[v].append(u)
    if not all(len(a) == 4 for a in adj): continue
    g = girth(adj); c4 = count4(adj)
    key = (g, -c4)
    if best is None or key > best[0]: best = (key, sorted(edges))
key, edges = best
with open(out, 'w') as f:
    f.write(f"{b} {len(edges)}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print(f"b={b} girth={key[0]} c4={-key[1]} file={out}")
