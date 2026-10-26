import sys, os
os.environ["OMP_NUM_THREADS"] = "1"; os.environ["OPENBLAS_NUM_THREADS"] = "1"
sys.argv = ['x', '4', '2', '1', '1']
exec(open('hubsearch.py').read().split('Y = random_Y()')[0])
import collections
# base graph (no Y): distances from every hub (rows) to all vertices, capped at 6
Ab = B0.copy()
V = I[HUBS].copy()
dist = np.full((len(HUBS), N), 99)
dist[np.arange(len(HUBS)), np.array(HUBS)] = 0
cur = V.copy()
for t in range(1, 8):
    cur = np.minimum(cur + cur @ Ab, 1.0)
    newly = (cur > 0) & (dist == 99)
    dist[newly] = t
hub_idx = {h: i for i, h in enumerate(HUBS)}
c = collections.Counter()
for i, h in enumerate(HUBS):
    kind = 'B' if (h - nv) < K else 'A'
    for h2 in HUBS:
        if h2 == h: continue
        k2 = 'B' if (h2 - nv) < K else 'A'
        c[(kind, k2, int(dist[i, h2]))] += 1
print('base hub-hub distance counts (kind, kind2, dist):', sorted(c.items()))
