"""Split Cayley hexagon H(q) for any prime power q (built for even q; char 2 included).

Same model as research/p4/hats/hexbig_gf.py: points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q) (in characteristic 2 the
sign is irrelevant), lines through x = lines through x of the plane pi_x cut out by Tits' six equations and the polar
form B(x, y) = 0 (B has no X3 term in characteristic 2).  Cached in cache/hex_q{q}.npz.

    from hexq import load;  H = load(q)   # H.F (field tables), H.P (N x 7), H.lines (N x q+1), H.through (N x q+1)
"""
import itertools
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402


class Field:
    def __init__(self, q):
        F = lib.GF(q)
        self.q, self.p = q, F.p
        self.ADD, self.MUL, self.NEG = F.add_table, F.mul_table, F._neg
        self.INV = np.zeros(q, dtype=np.int64)
        for x in range(1, q):
            self.INV[x] = next(y for y in range(1, q) if self.MUL[x, y] == 1)
        self.exp, self.log = F._exp, F._log

    def fsum(self, arrs):
        out = arrs[0]
        for a in arrs[1:]:
            out = self.ADD[out, a]
        return out


def _tr2(F, x):
    """absolute trace for characteristic 2: x + x^2 + x^4 + ..."""
    e = int(round(np.log2(F.q)))
    t, y = 0, int(x)
    for _ in range(e):
        t ^= y
        y = int(F.MUL[y, y])
    return t


class Hexagon:
    pass


PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def build(q, log=print):
    F = Field(q)
    ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
    inv = INV.tolist()
    POW = q ** np.arange(7, dtype=np.int64)
    pts = []
    for f in range(7):
        k = 6 - f
        grid = np.array(list(itertools.product(range(q), repeat=k)), dtype=np.int64) if k else np.zeros((1, 0), np.int64)
        V = np.zeros((len(grid), 7), dtype=np.int64)
        V[:, f] = 1
        V[:, f + 1:] = grid
        Qv = F.fsum([MUL[V[:, 0], V[:, 4]], MUL[V[:, 1], V[:, 5]], MUL[V[:, 2], V[:, 6]], NEG[MUL[V[:, 3], V[:, 3]]]])
        pts.append(V[Qv == 0])
    P = np.concatenate(pts)
    codes = P @ POW
    order = np.argsort(codes)
    P, codes = P[order], codes[order]
    N = len(P)
    assert N == (q ** 6 - 1) // (q - 1), N

    def normalize(V):
        first = np.argmax(V != 0, axis=1)
        lead = V[np.arange(len(V)), first]
        return MUL[V, INV[lead][:, None]]

    def index_of(V):
        c = normalize(V) @ POW
        i = np.searchsorted(codes, c)
        assert np.all(codes[np.minimum(i, N - 1)] == c), 'not a point'
        return i

    def system(x):
        M = np.zeros((7, 7), dtype=np.int64)
        for r, ((i, j), (k, l)) in enumerate(PAIRS):
            M[r, j] = ADD[M[r, j], x[i]]; M[r, i] = ADD[M[r, i], NEG[x[j]]]
            M[r, l] = ADD[M[r, l], NEG[x[k]]]; M[r, k] = ADD[M[r, k], x[l]]
        M[6] = [x[4], x[5], x[6], NEG[ADD[x[3], x[3]]], x[0], x[1], x[2]]
        return M

    def nullspace(M):
        M = M.copy()
        rows, piv = 0, []
        for col in range(M.shape[1]):
            r = next((r for r in range(rows, M.shape[0]) if M[r, col]), None)
            if r is None:
                continue
            M[[rows, r]] = M[[r, rows]]
            M[rows] = MUL[M[rows], inv[M[rows, col]]]
            for r2 in range(M.shape[0]):
                if r2 != rows and M[r2, col]:
                    M[r2] = ADD[M[r2], NEG[MUL[M[r2, col], M[rows]]]]
            piv.append(col)
            rows += 1
        free = [c for c in range(M.shape[1]) if c not in piv]
        basis = []
        for fcol in free:
            y = np.zeros(M.shape[1], dtype=np.int64)
            y[fcol] = 1
            for r, pc in enumerate(piv):
                y[pc] = NEG[M[r, fcol]]
            basis.append(y)
        return basis

    S_all = np.arange(q)
    line_pts = []
    t0 = time.time()
    for xi in range(N):
        x = P[xi]
        B = nullspace(system(x))
        assert len(B) == 3, (xi, len(B))
        best = None
        for u, w in itertools.combinations(B, 2):
            if len(nullspace(np.array([x, u, w]).T.copy())) == 0:
                best = (u, w)
                break
        assert best is not None
        u, w = best
        for y in [ADD[u, MUL[t, w]] for t in range(q)] + [w]:
            V = np.vstack([ADD[y[None, :], MUL[S_all[:, None], x[None, :]]], x[None, :]])
            idx = index_of(V)
            if idx.min() == xi:
                line_pts.append(np.sort(idx))
        if xi % 50000 == 0:
            log(f'[{time.time()-t0:.0f}s] point {xi}/{N} lines {len(line_pts)}')
    lines = np.array(line_pts)
    assert len(lines) == N, len(lines)
    return P, lines


def load(q, log=print):
    cache = HERE / 'cache' / f'hex_q{q}.npz'
    if cache.exists():
        d = np.load(cache)
        P, lines = d['P'], d['lines']
    else:
        P, lines = build(q, log)
        cache.parent.mkdir(exist_ok=True)
        np.savez_compressed(cache, P=P, lines=lines)
    H = Hexagon()
    H.q, H.F, H.P, H.lines, H.N = q, Field(q), P, lines, len(P)
    H.tr = (lambda x: _tr2(H.F, x)) if H.F.p == 2 else None
    N = H.N
    H.through = np.argsort(lines.ravel(), kind='stable').reshape(N, q + 1) // (q + 1)
    lkey = lines[:, 0].astype(np.int64) * N + lines[:, 1]
    H.lord = np.argsort(lkey)
    H.lkey_sorted = lkey[H.lord]
    POW = q ** np.arange(7, dtype=np.int64)
    H.codes = P @ POW
    return H


def write_incidence(H, path):
    N, q = H.N, H.q
    with open(path, 'w') as fh:
        fh.write(f'{2 * N}\n')
        for k in range(N):
            for p in H.lines[k]:
                fh.write(f'{p} {N + k}\n')


if __name__ == '__main__':
    q = int(sys.argv[1])
    H = load(q)
    print('q', q, 'points', H.N, 'lines', len(H.lines))
    if len(sys.argv) > 2:
        write_incidence(H, sys.argv[2])
        print('wrote', sys.argv[2])
