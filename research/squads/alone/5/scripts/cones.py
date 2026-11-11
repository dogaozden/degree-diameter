# For sampled edges (u,v): cone = same-side targets of u that go from distance <=5 to >5 when (u,v) is deleted;
# report cone size and the best coverage of the cone by any other neighbour w of u (B-centre ball radius 3).
import numpy as np, random
from collections import deque
from graph import load
n, adj, E = load('base.e'); nA = n // 2
C = np.load('C3.npy')
rnd = random.Random(11)
def cone(u, v):
    d = [-1] * n; d[u] = 0; q = deque([u])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if (x == u and y == v) or (x == v and y == u): continue
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    same = range(nA) if u < nA else range(nA, n)
    return [t for t in same if d[t] < 0 or d[t] > 5]
res = []
for _ in range(12):
    u, v = rnd.choice(E)
    if rnd.random() < 0.5: u, v = v, u
    L = cone(u, v)
    if u < nA:   # A-vertex u: its cone lies on A; centres are B-vertices adjacent to u
        ids = [w for w in adj[u] if w != v]
        Lc = np.array(L) if L else np.array([], dtype=int)
        best = max((int(C[w - nA, Lc].sum()) for w in ids), default=0) if len(Lc) else 0
    else:         # B-vertex u: cone on B, centres are A-vertices (use C transposed: C[b, a] with a = centre)
        ids = [w for w in adj[u] if w != v]
        Lc = np.array([t - nA for t in L]) if L else np.array([], dtype=int)
        best = max((int(C[Lc, w].sum()) for w in ids), default=0) if len(Lc) else 0
    res.append((len(L), best))
    print('u', u, 'side', 'A' if u < nA else 'B', 'cone', len(L), 'best other neighbour covers', best, flush=True)
