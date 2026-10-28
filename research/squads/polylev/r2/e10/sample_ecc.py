"""Diagnostic only (not a certification): BFS eccentricities from sampled sources. usage: sample_ecc.py EDGES NSRC SEED"""
import sys
import numpy as np
from collections import deque
fn, ns, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
with open(fn) as f:
    n = int(f.readline())
E = np.loadtxt(f.name, skiprows=1, dtype=np.int64) if False else np.loadtxt(fn, skiprows=1, dtype=np.int64)
U = np.concatenate([E[:, 0], E[:, 1]]); W = np.concatenate([E[:, 1], E[:, 0]])
order = np.argsort(U, kind='stable'); U = U[order]; W = W[order]
ptr = np.searchsorted(U, np.arange(n + 1))
rng = np.random.default_rng(seed)
src = rng.choice(n, size=ns, replace=False)
ecc = []
for s in src:
    dist = np.full(n, -1, dtype=np.int64); dist[s] = 0
    frontier = np.array([s]); d = 0
    while frontier.size:
        nb = np.concatenate([W[ptr[x]:ptr[x + 1]] for x in frontier])
        nb = np.unique(nb); nb = nb[dist[nb] < 0]
        d += 1
        dist[nb] = d
        frontier = nb
    assert (dist >= 0).all()
    ecc.append(int(dist.max()))
print(fn, 'sampled eccentricities: max', max(ecc), 'min', min(ecc), 'mean', round(sum(ecc)/len(ecc), 2), 'n', n, 'nsrc', ns)
