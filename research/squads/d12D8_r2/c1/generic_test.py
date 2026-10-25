#!/usr/bin/env python3
"""c1/generic_test.py: same Omega-B1 reading as build.py, for an arbitrary bipartite base B1 with
n points (side A, ids 0..n-1) and n lines (side B, ids n..2n-1), given by its edge list.
Used on small base graphs (e.g. the cycle C_2m, degree 2, diameter m) to test the thesis bound D <= D1 + 2
for alpha = 2 (copy-vertex degree Delta1 + 2 = 4 = 2*alpha) with the two figure patterns.
Usage: python3 generic_test.py cycle M PATTERN SIDE MAPS   (alpha = 2, so PATTERN has 2 letters)
"""
import sys
import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import shortest_path


def label_rule(pat, kind, j):
    if pat == 'a':
        if kind == 'U':
            return 'inner', [(j - 1) % 5, (j + 1) % 5]
        return 'outer', [(j + 2) % 5, (j + 3) % 5]
    if pat == 'b':
        if kind == 'U':
            return 'outer', [(j + 3) % 5, (j + 4) % 5]
        return 'inner', [(j - 1) % 5, (j + 1) % 5]
    raise ValueError(pat)


def build_generic(n, base_edges, pattern, side, maps, seed=1):
    alpha = len(pattern)
    G = 5 * alpha
    N1 = 2 * n
    rng = np.random.default_rng(seed)
    if maps == 'id':
        phi = np.tile(np.arange(n), (G, 1)); psi = np.tile(np.arange(n), (G, 1))
    elif maps == 'rand':
        phi = np.tile(np.arange(n), (G, 1)); psi = np.tile(rng.permutation(n), (G, 1))
    elif maps == 'both':
        phi = np.tile(rng.permutation(n), (G, 1)); psi = np.tile(rng.permutation(n), (G, 1))
    else:
        raise ValueError(maps)
    E = []
    for c in range(G):
        E.append(base_edges + c * N1)
    NEW0 = G * N1
    rows_a, rows_b = [], []
    for g in range(alpha):
        for kind in ('U', 'B'):
            for j in range(5):
                port, rel = label_rule(pattern[g], kind, j)
                lam = j if kind == 'U' else 5 + j
                for k in range(n):
                    for r in rel:
                        c = 5 * g + r
                        if side == 'P':
                            base = int(phi[c][k]) if port == 'outer' else n + int(psi[c][k])
                        else:
                            base = n + int(psi[c][k]) if port == 'outer' else int(phi[c][k])
                        rows_a.append(NEW0 + 10 * k + lam)
                        rows_b.append(c * N1 + base)
    new_edges = np.stack([np.array(rows_a, dtype=np.int64), np.array(rows_b, dtype=np.int64)], axis=1)
    allE = np.concatenate(E + [new_edges], axis=0)
    N = NEW0 + 10 * n
    return N, allE


def diameter(N, E):
    a, b = E[:, 0], E[:, 1]
    A = sp.coo_matrix((np.ones(2 * len(a)), (np.r_[a, b], np.r_[b, a])), shape=(N, N)).tocsr()
    D = shortest_path(A, method='D', directed=False, unweighted=True)
    return D.max(), np.isfinite(D).all()


if __name__ == '__main__':
    kind, m, pat, side, maps = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5]
    assert kind == 'cycle' and m % 2 == 0
    n = m                                   # points 0..m-1 (vertices 2i of C_2m), lines m..2m-1 (vertices 2i+1)
    base = []
    for i in range(m):
        base.append((i, n + i))             # line i ~ point i
        base.append((n + i, (i + 1) % m))   # line i ~ point i+1
    base = np.array(base, dtype=np.int64)
    N, E = build_generic(n, base, pat, side, maps)
    d, conn = diameter(N, E)
    print(f"cycle C_{2*m} (D1={m}) alpha=2 pattern={pat} side={side} maps={maps}: N={N} connected={conn} "
          f"diameter={int(d)}  D1+2={m+2}")
