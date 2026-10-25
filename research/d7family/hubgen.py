#!/usr/bin/env python3
"""hubgen.py: random bipartite hub graph between KB line-side and KA point-side hubs, max degree DH on both sides,
min(KB, KA)*DH edges (the larger side gets degrees DH and DH-1), simple (configuration model, repeated pairs re-drawn).
usage: hubgen.py KB KA DH SEED OUT.txt"""
import sys, numpy as np
KB, KA, DH, seed = (int(x) for x in sys.argv[1:5]); out = sys.argv[5]
rng = np.random.default_rng(seed)
M = min(KB, KA) * DH
def stubs(K):
    d = np.full(K, M // K); d[rng.permutation(K)[:M - d.sum()]] += 1
    assert d.max() <= DH and d.sum() == M
    return np.repeat(np.arange(K), d)
a, b = stubs(KB), stubs(KA)
for it in range(200):
    b = b[rng.permutation(M)] if it == 0 else b
    key = a * KA + b
    o = np.argsort(key, kind='stable'); ks = key[o]
    dup = np.zeros(M, bool); dup[o[1:][ks[1:] == ks[:-1]]] = True
    nd = dup.sum()
    if nd == 0: break
    # swap each duplicate's point-side end with a random edge's
    idx = np.nonzero(dup)[0]; oth = rng.integers(0, M, len(idx))
    b[idx], b[oth] = b[oth].copy(), b[idx].copy()
assert len(np.unique(a * KA + b)) == M
np.savetxt(out, np.stack([a, b], axis=1), fmt='%d')
print(f'hub graph {KB} x {KA}, {M} edges, degrees line-side {np.bincount(a).min()}..{np.bincount(a).max()}, '
      f'point-side {np.bincount(b).min()}..{np.bincount(b).max()}')
