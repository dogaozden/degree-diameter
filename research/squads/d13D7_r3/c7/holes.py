"""Hole-pattern view (card c7).  For a pattern z in F_11^{122} (one hole value per direction n in E), let
A_z = {v in V : n.v != z_n for all n}.  Any clique K inside A_z has cov(K)=0, so F(K) = 11|K| + 122.
This module computes A_z and the clique number of G[A_z] exactly (small graphs)."""
import sys, os, itertools, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import directions
Q = 11
D = directions()                      # 122 x 4
V4 = np.array([(s, b, c, f) for s in range(Q) for b in range(Q) for c in range(Q) for f in range(Q)], dtype=np.int64)
def vid(v):
    s, b, c, f = v
    return s * 1331 + b * 121 + c * 11 + f
RES = (D @ V4.T) % Q                  # 122 x 14641 residues n.v
NSQ = np.zeros(Q, bool); NSQ[[2, 6, 7, 8, 10]] = True
def adjacent_matrix(idx):
    X = V4[idx]
    diff = (X[:, None, :] - X[None, :, :]) % Q
    Dv = (diff[..., 0]**2 + 3*diff[..., 2]**2 + 8*diff[..., 1]*diff[..., 3]) % Q
    return NSQ[Dv]
def A_of_pattern(z):
    ok = np.all(RES != np.asarray(z)[:, None], axis=0)
    return np.nonzero(ok)[0]
def max_clique(adj):
    """exact maximum clique (Tomita-style colouring B&B) on a boolean adjacency matrix"""
    n = adj.shape[0]
    best = []
    def expand(R, P):
        nonlocal best
        # greedy colouring bound
        order, colour = [], []
        Pl = list(P); c = 0
        while Pl:
            c += 1
            Q_ = []
            rest = []
            for v in Pl:
                if all(not adj[v, u] for u in Q_):
                    Q_.append(v)
                else:
                    rest.append(v)
            for v in Q_:
                order.append(v); colour.append(c)
            Pl = rest
        for i in range(len(order) - 1, -1, -1):
            if len(R) + colour[i] <= len(best):
                return
            v = order[i]
            newP = [u for u in P if adj[v, u]]
            R2 = R + [v]
            if not newP:
                if len(R2) > len(best): best = R2[:]
            else:
                expand(R2, newP)
            P = [u for u in P if u != v]
    expand([], list(range(n)))
    return best
if __name__ == '__main__':
    pass
