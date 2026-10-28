"""linetrace2.py: for a line trace L^M of H(q), count the lines at distance 6 (opposite) from every trace line, and
greedily add lines until the set 4-dominates all lines. Usage: python3 linetrace2.py HEXBIN TRIALS SEED"""
import sys
import numpy as np
from hexlib import Hex

H = Hex(sys.argv[1]); T = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
N, L = H.N, H.L
adj = H.adjacency(); H._adj = adj


def ball4(v):
    """lines within distance 4 of line vertex v (as line indices)"""
    s = {v}; fr = [v]
    for _ in range(4):
        nb = set(adj[fr].ravel().tolist()) - s; s |= nb; fr = list(nb)
    return np.array([x - N for x in s if x >= N])


for t in range(T):
    a = N + int(rng.integers(L)); da = H.bfs(a)
    b = N + int(rng.choice(np.where(da[N:] == 6)[0])); db = H.bfs(b)
    tr = [v for v in range(N, N + L) if da[v] == 2 and db[v] == 4]
    cov = np.zeros(L, dtype=bool)
    for v in tr:
        cov[ball4(v)] = True
    U = np.where(~cov)[0]
    extra = []
    while (~cov).any():
        # candidate lines: those dominating the most uncovered lines, among lines near an uncovered line
        u = np.where(~cov)[0]
        cand = np.unique(np.concatenate([ball4(N + int(x)) for x in rng.choice(u, size=min(5, len(u)), replace=False)]))
        best = max(cand, key=lambda c: (~cov[ball4(N + int(c))]).sum())
        extra.append(int(best)); cov[ball4(N + int(best))] = True
    print(f'q={H.q}: trace undominated {len(U)}; greedy extra lines {len(extra)} -> class size {len(tr) + len(extra)}', flush=True)
