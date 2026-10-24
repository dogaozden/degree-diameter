"""hexlib.py: load H(q) from hexgen's hex/hex_q{q}.bin and write base graphs for lifteval (cell-14-8 job).

H(q): N points = N lines, line l has points LP[l, 0..q]; PL[p] = lines through p.
Base graph for lifteval: side A = points 0..N-1, side B = lines 0..N-1, edges (p, l, voltage).
"""
import numpy as np
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(q):
    raw = np.fromfile(HERE / 'hex' / f'hex_q{q}.bin', dtype=np.int32, count=3)
    qq, N, L = (int(x) for x in raw)
    LP = np.fromfile(HERE / 'hex' / f'hex_q{q}.bin', dtype=np.int32, count=3 + L * (q + 1))[3:].reshape(L, q + 1)
    coord = np.fromfile(HERE / 'hex' / f'hex_q{q}.bin', dtype=np.uint8, offset=12 + 4 * L * (q + 1)).reshape(N, 7)
    PL = np.zeros((N, q + 1), dtype=np.int32)
    cnt = np.zeros(N, dtype=np.int32)
    for l in range(L):
        for p in LP[l]:
            PL[p, cnt[p]] = l
            cnt[p] += 1
    assert (cnt == q + 1).all()
    return N, LP, PL, coord


def write_base(fn, N, m, edges):
    """edges: array (E, 3) of (point, line, voltage)."""
    with open(fn, 'w') as f:
        f.write(f'{N} {N} {m}\n')
        np.savetxt(f, np.asarray(edges, dtype=np.int64) % [N * 10, N * 10, m], fmt='%d')


def hex_edges(LP, volt=None):
    """flags (p, l) with voltage volt[l, k] (k = position of p on l), default 0."""
    L, Q1 = LP.shape
    ls = np.repeat(np.arange(L), Q1)
    ps = LP.reshape(-1)
    v = np.zeros(L * Q1, dtype=np.int64) if volt is None else np.asarray(volt).reshape(-1)
    return np.stack([ps, ls, v], axis=1)


def dist_from_point(p, LP, PL, maxd=6):
    """BFS distances in the incidence graph from point p: (dp over points, dl over lines)."""
    N = PL.shape[0]
    dp = np.full(N, 99, dtype=np.int8)
    dl = np.full(N, 99, dtype=np.int8)
    dp[p] = 0
    front_p = np.array([p])
    d = 0
    while d < maxd:
        ls = np.unique(PL[front_p].reshape(-1))
        ls = ls[dl[ls] == 99]
        d += 1
        dl[ls] = d
        if d >= maxd or len(ls) == 0:
            break
        ps = np.unique(LP[ls].reshape(-1))
        ps = ps[dp[ps] == 99]
        d += 1
        dp[ps] = d
        front_p = ps
    return dp, dl
