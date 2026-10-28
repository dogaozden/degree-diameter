"""linetrace.py: are the line traces L^M (L, M opposite lines; the q+1 lines at distance 2 from L and 4 from M)
4-dominating on the lines of H(q)?  Also checks point traces x^y on the point side (control).
Usage: python3 linetrace.py HEXBIN TRIALS SEED"""
import sys
import numpy as np
from hexlib import Hex

H = Hex(sys.argv[1]); T = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
N, L = H.N, H.L
adj = H.adjacency(); H._adj = adj


def msbfs(src):
    n = adj.shape[0]; d = np.full(n, -1, dtype=np.int64); d[src] = 0; fr = np.array(src); k = 0
    while len(fr):
        k += 1; nb = np.unique(adj[fr].ravel()); nb = nb[d[nb] < 0]; d[nb] = k; fr = nb
    return d


for side, off, cnt in (('lines', N, L), ('points', 0, N)):
    good = 0
    for t in range(T):
        a = off + int(rng.integers(cnt)); da = H.bfs(a)
        opp = np.where(da[off:off + cnt] == 6)[0]
        b = off + int(rng.choice(opp)); db = H.bfs(b)
        tr = [v for v in range(off, off + cnt) if da[v] == 2 and db[v] == 4]
        d = msbfs(tr)
        far = int((d[off:off + cnt] > 4).sum())
        good += far == 0
        if t < 3:
            print(f'q={H.q} {side}: trace size {len(tr)}, {far} {side} at distance > 4 (max {int(d[off:off+cnt].max())})')
    print(f'q={H.q} {side}: {good}/{T} traces 4-dominating', flush=True)
