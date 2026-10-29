"""Build the partial ovoid e4 + union of the lines for a clique (vertex indices of graph.py's coset list) and
verify it by computing B on all pairs of the 7-coordinate points (direct formula, not the Qp shortcut).
usage: verify_set.py <p> <clique-file>   (clique-file: whitespace-separated vertex indices)"""
import sys, numpy as np
from graph import build
from hexaffine import point7, B7, Q7

def verify(p, clique):
    u, R, adj = build(p)
    pts = [np.array([0, 0, 0, 0, 1, 0, 0], dtype=np.int64)]   # e4
    for v in clique:
        c = [int(t) for t in R[v]]
        for lam in range(p):
            pts.append(point7([(c[i] + lam * u[i]) % p for i in range(5)], p))
    P = np.array(pts, dtype=np.int64)
    assert all(Q7(x, p) == 0 for x in P), 'point off the quadric'
    # Gram matrix of B on all pairs, direct 7-coordinate formula
    G = (P[:, None, 0] * P[None, :, 4] + P[:, None, 4] * P[None, :, 0] + P[:, None, 1] * P[None, :, 5]
         + P[:, None, 5] * P[None, :, 1] + P[:, None, 2] * P[None, :, 6] + P[:, None, 6] * P[None, :, 2]
         - 2 * P[:, None, 3] * P[None, :, 3]) % p
    n = len(P)
    off = G[~np.eye(n, dtype=bool)]
    distinct = len({tuple(x) for x in P.tolist()}) == n
    ok = bool(distinct and (off != 0).all())
    return {'p': p, 'k_lines': len(clique), 'n_points': n, 'distinct': distinct,
            'pairwise_opposite_all_pairs': ok, 'u': list(u)}

if __name__ == '__main__':
    p = int(sys.argv[1])
    clique = [int(t) for t in open(sys.argv[2]).read().split()]
    print(verify(p, clique))
