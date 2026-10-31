# usage: mkunbal.py IN OUT NADD_SIDE0 NADD_SIDE1 SEED
# Adds NADD_SIDE0 new vertices of colour 0 and NADD_SIDE1 of colour 1 to a bipartite graph (colours from BFS at vertex 0).
# Each new vertex u of colour c takes 6 neighbours w of colour 1-c; each w loses one edge (w,z) to a colour-c vertex z
# (so w keeps degree 6 and z becomes deficient). Result: max degree 6, possibly unbalanced sides.
import sys, random
from collections import deque
fn, out, na0, na1, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
random.seed(seed)
t = open(fn).read().split(); n = int(t[0]); E = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
adj = [set() for _ in range(n)]
for a, b in E: adj[a].add(b); adj[b].add(a)
col = [-1]*n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
E = set(tuple(sorted(e)) for e in E)
n2 = n
newv = [(0, na0), (1, na1)]
adjc = {v: set(adj[v]) for v in range(n)}
for c, cnt in newv:
    for _ in range(cnt):
        u = n2; n2 += 1; adjc[u] = set()
        # 6 neighbours of colour 1-c, each losing one edge to a colour-c vertex
        cands = [w for w in range(n) if col[w] == 1-c and len(adjc[w]) == 6 and not any(z in adjc[u] for z in [])]
        ws = random.sample(cands, 6)
        for w in ws:
            zs = [z for z in adjc[w] if col[z] == c]
            z = random.choice(zs)
            adjc[w].discard(z); adjc[z].discard(w)
            E.discard(tuple(sorted((w, z))))
            adjc[w].add(u); adjc[u].add(w); E.add(tuple(sorted((w, u))))
        col.append(c)
with open(out, 'w') as f:
    f.write("%d\n" % n2)
    for a, b in sorted(E): f.write("%d %d\n" % (a, b))
deg = [len(adjc[v]) for v in range(n2)]
from collections import Counter
print("n", n2, "edges", len(E), "deg", sorted(Counter(deg).items()), "sides", Counter(col[:n2]))
