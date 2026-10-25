"""Small helpers for the split Cayley hexagon H(q) file written by hexgen (hex/hex_q11.bin).
Points of H(q) = points of the quadric Q(x) = x0x4 + x1x5 + x2x6 - x3^2 in PG(6,q); a point is stored by its index
0..N-1 and its 7 coordinates (first nonzero = 1).  Lines are stored as (q+1)-tuples of point indices.
Facts used (checked in check_facts()): two points are at distance <= 4 in the incidence graph iff B(x,y) = 0,
i.e. they are opposite (distance 6) iff B(x,y) != 0, where B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3."""
import numpy as np, sys, os

def load(path=None):
    if path is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', 'hex_q11.bin')
    raw = open(path, 'rb').read()
    q, N, L = np.frombuffer(raw[:12], dtype=np.int32)
    lines = np.frombuffer(raw[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1)
    coord = np.frombuffer(raw[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return int(q), lines, coord

def bilinear(X, Y, q):
    """B(x,y) mod q for rows of X against rows of Y (broadcasting)."""
    return (X[..., 0] * Y[..., 4] + X[..., 4] * Y[..., 0] + X[..., 1] * Y[..., 5] + X[..., 5] * Y[..., 1]
            + X[..., 2] * Y[..., 6] + X[..., 6] * Y[..., 2] - 2 * X[..., 3] * Y[..., 3]) % q

def gram(coord, idx, q):
    P = coord[np.asarray(idx)]
    return bilinear(P[:, None, :], P[None, :, :], q)

def is_partial_ovoid(coord, idx, q):
    """True iff the points idx are pairwise opposite in H(q) (pairwise non-orthogonal)."""
    idx = list(idx)
    if len(set(idx)) != len(idx): return False
    G = gram(coord, idx, q)
    np.fill_diagonal(G, 1)
    return bool((G != 0).all())

def point_lines(lines, N):
    pl = [[] for _ in range(N)]
    for l, pts in enumerate(lines):
        for p in pts: pl[p].append(l)
    return np.array(pl, dtype=np.int64)

if __name__ == '__main__':
    q, lines, coord = load()
    print('q', q, 'points', len(coord), 'lines', len(lines))
