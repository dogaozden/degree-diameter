"""e13 common: load H(q) from the lab binary, build line-line 4-balls (incidence distance <= 4) and pencils."""
import sys, os
import numpy as np
LAB = '/home/user/degree-diameter/research/theorems/polylev'
sys.path.insert(0, LAB)
from hexlib import Hex


def load(q):
    return Hex(f'{LAB}/hex/hex_q{q}.bin')


def ball_matrix(H):
    """B[L, M] = True iff incidence distance(line L, line M) <= 4 (includes L == M). Lines indexed 0..L-1."""
    N, Lc = H.N, H.L
    adj = H.adjacency()
    B = np.zeros((Lc, Lc), dtype=bool)
    for l in range(Lc):
        d = np.full(N + Lc, -1, dtype=np.int64)
        d[N + l] = 0
        fr = np.array([N + l])
        for k in range(1, 5):
            nb = np.unique(adj[fr].ravel())
            nb = nb[d[nb] < 0]
            d[nb] = k
            fr = nb
        B[l] = d[N:] >= 0
    return B


def ball_matrix_cached(H, q):
    fn = f'/home/user/degree-diameter/research/squads/polylev/r2/e13/ball4_q{q}.npy'
    if os.path.exists(fn):
        return np.load(fn)
    B = ball_matrix(H)
    np.save(fn, B)
    return B


def pencil_sets(H):
    """list of (point, sorted list of its q+1 lines)."""
    return [(p, sorted(H.PL[p].tolist())) for p in range(H.N)]
