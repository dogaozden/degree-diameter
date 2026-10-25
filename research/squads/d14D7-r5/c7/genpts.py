#!/usr/bin/env python3
"""genpts.py: write point lists of Q(6,11) (normalized, singular) for the c7 searches.
usage: genpts.py all OUT | hyp OUT [a b c d e f g] | chart OUT
  all : all 177156 points
  hyp : points of Q(6,11) with B(x,v)=0 for v = e0+e4 (x0+x4 = 0), elliptic hyperplane section (expect 15984)
  chart: affine chart x0=1 (161051 points, expensive to conflict-check; not used directly)"""
import sys, numpy as np
q = 11
def all_points():
    out = []
    for p in range(7):
        free = 6 - p
        if free == 0:
            grid = np.zeros((1, 0), dtype=np.int64)
        else:
            g = np.indices((q,) * free).reshape(free, -1).T.astype(np.int64)
            grid = g
        m = grid.shape[0]
        X = np.zeros((m, 7), dtype=np.int64)
        X[:, p] = 1
        X[:, p + 1:] = grid
        out.append(X)
    X = np.vstack(out)
    Qv = (X[:, 0] * X[:, 4] + X[:, 1] * X[:, 5] + X[:, 2] * X[:, 6] - X[:, 3] ** 2) % q
    return X[Qv == 0]
if __name__ == "__main__":
    mode, path = sys.argv[1], sys.argv[2]
    P = all_points()
    assert len(P) == 177156, len(P)
    if mode == "all":
        sel = P
    elif mode == "hyp":
        sel = P[(P[:, 0] + P[:, 4]) % q == 0]
    else:
        raise SystemExit("unknown mode")
    np.savetxt(path, sel, fmt="%d")
    print(mode, "wrote", len(sel), "points to", path)
