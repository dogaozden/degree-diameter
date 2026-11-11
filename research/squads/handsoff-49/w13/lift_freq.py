"""Lift analysis: base mh2_1 (4 vertices: 0,1 side A; 2,3 side B; 8 edges). Random voltages.
For root (0,e): which group elements x make (u,x) within distance 8 (same side) or 9 (other side)?
Counts how often each (u, x) is reached, to find rare elements (the obstruction)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
m, k, r, samples = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
T = meta_table(m, k, r); Sinv = inverses(T); N = T.shape[0]
base = [(0,2),(0,2),(0,3),(0,3),(1,2),(1,2),(1,3),(1,3)]
rng = np.random.default_rng(7)
from collections import deque
cnt = np.zeros((4, N), int)
show = lambda x: (int(x % m), int(x // m))
for it in range(samples):
    volt = rng.integers(0, N, size=len(base))
    # adjacency of lift: vertex (u,x) -> id u*N + x
    adj = [[] for _ in range(4 * N)]
    for (e, (u, v)) in enumerate(base):
        g = volt[e]
        for x in range(N):
            a = u * N + x; b = v * N + T[g, x]
            adj[a].append(b); adj[b].append(a)
    dist = np.full(4 * N, -1); dist[0] = 0; dq = deque([0])
    while dq:
        y = dq.popleft()
        if dist[y] >= 9: continue
        for z in adj[y]:
            if dist[z] < 0:
                dist[z] = dist[y] + 1; dq.append(z)
    for u in range(4):
        ok = (dist[u*N:(u+1)*N] >= 0) & (dist[u*N:(u+1)*N] <= 9)
        cnt[u] += ok
np.save('/home/user/degree-diameter/research/squads/handsoff-49/w13/liftfreq_%d_%d_%d.npy' % (m, k, r), cnt)
for u in range(4):
    o = np.argsort(cnt[u])
    print("root-side vertex", u, "min reach", cnt[u].min(), "of", samples, "rarest:", [ (show(x), int(cnt[u][x])) for x in o[:6]])
