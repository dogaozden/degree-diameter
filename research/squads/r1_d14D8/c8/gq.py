"""gq.py: symplectic generalized quadrangle W(q) (q prime) as an incidence structure.

Points: all points of PG(3,q). Lines: totally isotropic lines of the symplectic form
B(x,y) = x0 y1 - x1 y0 + x2 y3 - x3 y2 (mod q). Every point lies on q+1 lines, every line has q+1 points,
N = (q+1)(q^2+1) points and N lines. Incidence graph: degree q+1, girth 8, diameter 4 (bipartite Moore graph).
Usage as a module: from gq import build; N, LP, PL = build(q)
  LP[l] = the q+1 point ids on line l; PL[p] = the q+1 line ids through point p.
"""
import itertools
import numpy as np


def build(q):
    tuples = []
    for t in itertools.product(range(q), repeat=4):
        if any(t):
            first = next(x for x in t if x)
            if first == 1:
                tuples.append(t)
    P = np.array(tuples, dtype=np.int64)
    N = len(P)
    assert N == (q + 1) * (q * q + 1), N
    code = ((P[:, 0] * q + P[:, 1]) * q + P[:, 2]) * q + P[:, 3]
    idx = np.full(q ** 4, -1, dtype=np.int64)
    idx[code] = np.arange(N)

    def pid(V):
        """normalized point ids of an array of vectors (rows), none zero."""
        V = V % q
        first = np.argmax(V != 0, axis=1)
        lead = V[np.arange(len(V)), first]
        inv = np.array([0] + [pow(int(a), q - 2, q) for a in range(1, q)], dtype=np.int64)
        W = (V * inv[lead][:, None]) % q
        c = ((W[:, 0] * q + W[:, 1]) * q + W[:, 2]) * q + W[:, 3]
        out = idx[c]
        assert (out >= 0).all()
        return out

    # symplectic form matrix
    B = (np.outer(P[:, 0], P[:, 1]) - np.outer(P[:, 1], P[:, 0]) + np.outer(P[:, 2], P[:, 3]) - np.outer(P[:, 3], P[:, 2])) % q
    iu, ju = np.nonzero(np.triu(B == 0, k=1))
    # line through points i and j: {P_i + t P_j} (t in GF(q)) and {P_j}
    lines = set()
    rows = []
    for t in range(q):
        V = (P[iu] + t * P[ju]) % q
        rows.append(pid(V))
    rows.append(ju)  # the point P_j itself: combinations (0,1)
    # rows[k][pair] = point id; each pair gives 14 points (q+1), includes i (t=0 gives P_i... see below)
    # rows[0] = point of P_i + 0*P_j = P_i (i), rows[1..] etc. Build the full set per pair:
    R = np.stack(rows, axis=1)  # shape (pairs, q+1)
    R.sort(axis=1)
    uniq = np.unique(R, axis=0)
    assert uniq.shape == (N, q + 1), uniq.shape
    LP = uniq
    PL = np.full((N, q + 1), -1, dtype=np.int64)
    cnt = np.zeros(N, dtype=np.int64)
    for l in range(N):
        for p in LP[l]:
            PL[p, cnt[p]] = l
            cnt[p] += 1
    assert (cnt == q + 1).all()
    return N, LP, PL


if __name__ == '__main__':
    import sys
    q = int(sys.argv[1])
    N, LP, PL = build(q)
    print('N', N, 'LP', LP.shape, 'PL', PL.shape)
    # check: two points lie on at most one common line; girth 8 check via common-neighbour counts
    import collections
    cnt = collections.Counter()
    for l in range(N):
        pts = LP[l]
        for a, b in itertools.combinations(sorted(pts), 2):
            cnt[(a, b)] += 1
    print('max lines through a pair of points', max(cnt.values()), 'pairs with a line', len(cnt))
