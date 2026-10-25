#!/usr/bin/env python3
"""hubsame.py: same-side distances in a bipartite hub graph (lines "a b", a < KB line-side, b < KA point-side). Prints
the number of ordered same-side pairs at distance > 6 inside the hub graph alone (a sufficient condition for the hub
part of the typed-level theorem; opposite-side hubs always meet within 7 through any level).
usage: hubsame.py HUBEDGES KB KA"""
import sys, numpy as np
he = np.loadtxt(sys.argv[1], dtype=np.int64).reshape(-1, 2); KB, KA = int(sys.argv[2]), int(sys.argv[3])
def nbl(a, b, K):
    o = np.argsort(a, kind='stable'); bs = b[o]; st = np.searchsorted(a[o], np.arange(K + 1)); dg = np.diff(st)
    assert dg.min() >= 1; dm = dg.max()
    return np.stack([bs[st[:-1] + np.minimum(t, dg - 1)] for t in range(dm)], axis=1)
bad = 0
for side in (0, 1):
    u, v, K, Kv = (he[:, 0], he[:, 1], KB, KA) if side == 0 else (he[:, 1], he[:, 0], KA, KB)
    Mu, Mv = nbl(u, v, K), nbl(v, u, Kv)
    W = (K + 63) // 64; idx = np.arange(K)
    Bt = np.zeros((K, W), np.uint64); Bt[idx, idx // 64] |= np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(3):
        U = Bt[Mv[:, 0]].copy()
        for t in range(1, Mv.shape[1]): U |= Bt[Mv[:, t]]
        Bn = Bt.copy()
        for t in range(Mu.shape[1]): Bn |= U[Mu[:, t]]
        Bt = Bn
    full = np.full(W, ~np.uint64(0), np.uint64)
    if K % 64: full[-1] = np.uint64((1 << (K % 64)) - 1)
    miss = Bt ^ full
    bad += int(sum(bin(int(w)).count('1') for w in miss[miss != 0]))
print(f'hub graph {KB} x {KA}, {len(he)} edges: {bad} same-side ordered pairs beyond 6')
