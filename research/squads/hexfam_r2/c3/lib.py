"""c4 library: group-orbit unions on points of Q(6,q) (= points of H(q)).
Groups given by 7x7 matrices M (isometries of A7) -> point permutations via Geo.perm.
Orbits via scipy connected components; self-compatible orbits; compat graph; exact max-weight clique."""
import sys, time, random, numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo, A7
from mwc import max_weight_clique

def orbit_labels(N, perms):
    rows = np.concatenate([np.arange(N)] * len(perms))
    cols = np.concatenate([np.asarray(p) for p in perms])
    g = coo_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(N, N))
    _, lab = connected_components(g, directed=True, connection='weak')
    return lab

def orbit_members(lab):
    counts = np.bincount(lab)
    order = np.argsort(lab, kind='stable')
    return np.split(order, np.cumsum(counts)[:-1]), counts

def reflection_matrix(v, q):
    v = np.asarray(v, dtype=np.int64) % q
    return (np.eye(7, dtype=np.int64) - np.outer(v, (A7 @ v) % q)) % q

def sc_and_compat(G, members, cap):
    """self-compatible orbits (size<=cap, pairwise opposite) and compat matrix among them."""
    q = G.q; C = G.C
    S = []
    for o, m in enumerate(members):
        if len(m) > cap or len(m) == 0: continue
        r = m[0]
        ok = ((C[r] @ A7 @ C[m].T) % q) != 0
        ok[0] = True
        if ok.all(): S.append(o)
    n = len(S)
    if n == 0: return S, np.zeros((0, 0), bool)
    sizes = np.array([len(members[o]) for o in S])
    order = np.concatenate([members[o] for o in S])
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    A = np.zeros((n, n), bool)
    for a, o in enumerate(S):
        r = members[o][0]
        ok = ((C[r] @ A7 @ C[order].T) % q) != 0
        A[a] = np.logical_and.reduceat(ok, starts)
    A = A & A.T
    np.fill_diagonal(A, False)
    return S, A

def best_union(members, S, A, tl=60):
    n = len(S); w = [len(members[o]) for o in S]
    adj = [0] * n
    for i in range(n):
        bits = 0
        for j in np.nonzero(A[i])[0]: bits |= 1 << int(j)
        adj[i] = bits
    wgt, verts, done = max_weight_clique(w, adj, tl)
    return wgt, [S[i] for i in verts], done

def evaluate(G, perms, cap, tl=60, label=''):
    """perms: list of point permutations (generators). returns (best weight, point ids, info)"""
    t0 = time.time()
    lab = orbit_labels(G.N, perms)
    members, counts = orbit_members(lab)
    S, A = sc_and_compat(G, members, cap)
    info = dict(label=label, orbits=len(members), selfcompat=len(S), secs=0.0)
    if len(S) == 0:
        info.update(best=0, exact=True, sizes=[]); info['secs'] = round(time.time() - t0, 1)
        return 0, [], info
    wgt, cl, done = best_union(members, S, A, tl)
    pts = sorted(int(p) for o in cl for p in members[o])
    info.update(best=wgt, exact=done, sizes=sorted(int(counts[o]) for o in cl), secs=round(time.time() - t0, 1))
    return wgt, pts, info

def check_set(G, pts):
    ok, ext = G.check_opp(np.asarray(pts))
    return ok, ext
