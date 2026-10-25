"""c1 (q=7 pool): mix good orbits of several subgroups of PSL(2,q), exact pairwise compatibility at point level.
Usage: python3 pool_c1.py Q T [tlimit]"""
import sys, time, random, json
import numpy as np
from scipy.sparse import coo_matrix, csr_matrix
from scipy.sparse.csgraph import connected_components
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r1/c1')
from q6lib import Geo, A7, inv_mod
from sl2rep import gram, sub_matrix
from orbits_c1 import subgroup_list, heur_clique
from mwc import max_weight_clique

def main(q, t, tlimit):
    t0 = time.time(); G = Geo(q); N = G.N
    T = G.to_std(gram(q)); Ti = inv_mod(T, q)
    def perm_of(x): return G.perm((T @ (sub_matrix(*x, q) % q) % q) @ Ti % q)
    rng = random.Random(11)
    subs = subgroup_list(q, t, rng, nconj=6)
    pool = {}   # key -> points
    for name, gens in subs:
        perms = [perm_of(x) for x in gens]
        nc, L = connected_components(coo_matrix((np.ones(N * len(perms), dtype=np.int8),
                                  (np.tile(np.arange(N), len(perms)), np.concatenate(perms))), shape=(N, N)),
                                  directed=True, connection='weak')
        rep = np.zeros(nc, dtype=np.int64); rep[L[::-1]] = np.arange(N)[::-1]
        rep_of_pt = rep[L]
        vals = ((G.C[rep_of_pt] @ A7) * G.C).sum(1) % q
        bad = np.bincount(L, weights=((vals == 0) & (np.arange(N) != rep_of_pt)).astype(np.float64), minlength=nc)
        good = np.nonzero(bad == 0)[0]
        order = np.argsort(L, kind='stable'); starts = np.searchsorted(L[order], np.arange(nc + 1))
        for o in good:
            pts = np.sort(order[starts[o]:starts[o + 1]])
            pool.setdefault(pts.tobytes(), pts)
        print('  %s: good orbits %d, pool now %d (%.0fs)' % (name, len(good), len(pool), time.time() - t0), flush=True)
    orbs = list(pool.values()); K = len(orbs)
    w = np.array([len(o) for o in orbs], dtype=np.float64)
    print('pool size K=%d, total points %d' % (K, sum(len(o) for o in orbs)), flush=True)
    # membership P (N x K) sparse
    rows = np.concatenate(orbs); cols = np.concatenate([np.full(len(o), i) for i, o in enumerate(orbs)])
    P = csr_matrix((np.ones(len(rows), dtype=np.float32), (rows, cols)), shape=(N, K))
    PT = P.T.tocsr()
    M = np.zeros((K, K), dtype=np.float64)
    CH = 400
    for s in range(0, N, CH):
        R = np.arange(s, min(N, s + CH))
        badR = ((G.C[R] @ A7) @ G.C.T % q == 0).astype(np.float32)   # c x N
        Z = (PT @ badR.T).T                                          # c x K  (= bad * P)
        M += np.asarray(P[R].T @ Z)
    comp = (M == 0); np.fill_diagonal(comp, False)
    print('compat density %.4f (%.0fs)' % (comp.sum() / max(1, K * (K - 1)), time.time() - t0), flush=True)
    hw, hv = heur_clique(w, comp, iters=600, rng=rng)
    bw, bv = hw, hv
    adj = [0] * K
    for i in range(K):
        bits = 0
        for j in np.nonzero(comp[i])[0]: bits |= 1 << int(j)
        adj[i] = bits
    ew, ev, exact = max_weight_clique(list(w.astype(int)), adj, tlimit=tlimit)
    print('heuristic %d, exact-search %d (%s)' % (hw, ew, 'exact' if exact else 'timeout'), flush=True)
    if ew > bw: bw, bv = ew, ev
    pts = sorted(set(np.concatenate([orbs[i] for i in bv]).tolist()))
    np.save('/home/user/degree-diameter/research/squads/hexfam_r1/c1/pool_best_q%d.npy' % q, np.array(pts))
    print('POOL BEST weight %d, points %d' % (bw, len(pts)), flush=True)

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]) if len(sys.argv) > 3 else 60.0)
