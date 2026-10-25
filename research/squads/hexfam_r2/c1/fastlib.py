import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from lib import *
import scipy.sparse as sp
from scipy.sparse.csgraph import connected_components
def forb(perm_list):
    rows = np.concatenate([np.arange(N) for _ in perm_list])
    cols = np.concatenate([p for p in perm_list])
    A = sp.coo_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(N, N))
    _, lab = connected_components(A, directed=True, connection='weak')
    return lab
def summarize(lab):
    K = lab.max() + 1
    sizes = np.bincount(lab, minlength=K)
    C = coll()
    conf = np.zeros((K, K), dtype=bool)
    conf[lab[:, None].repeat(90, 1).ravel(), lab[C].ravel()] = True
    bad = np.diag(conf).copy()
    return K, sizes, bad, conf
def mwis_exact(sizes, good_idx, conf, tlimit=20):
    """max-weight independent set among good orbits (conflict graph conf); returns (weight, list of orbit ids, exact)"""
    from mwc import max_weight_clique
    idx = list(good_idx)
    n = len(idx)
    adj = [0] * n
    sub = conf[np.ix_(idx, idx)]
    for a in range(n):
        bits = 0
        row = np.nonzero(~sub[a])[0]
        for b in row:
            if b != a: bits |= (1 << int(b))
        adj[a] = bits
    w = [int(sizes[i]) for i in idx]
    best, verts, exact = max_weight_clique(w, adj, tlimit)
    return best, [idx[v] for v in verts], exact
