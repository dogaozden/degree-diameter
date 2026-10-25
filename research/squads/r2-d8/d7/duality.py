"""Find dualities (colour-swapping distance-preserving bijections) of the incidence graph of H(q).

A duality phi maps points to lines and lines to points preserving all distances. Such phi is exactly a
point-line isomorphism H(q)^D -> H(q), so it exists only when H(q) is self-dual (q = 3^h).
Usage: python3 -I duality.py q seed out.npy [time_limit]
Vertex ids: points 0..N-1, lines N..2N-1 (as in gh.py).
"""
import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh

sys.setrecursionlimit(20000)


def assign(C, phi, v, w, D):
    phi[v] = w
    C[v, :] = False
    C[:, w] = False
    unm = phi < 0
    if unm.any():
        mask = (D[w, :][None, :] == D[:, v][:, None])
        C[unm] &= mask[unm]


def propagate(C, phi, D):
    """force singleton candidate sets; return False on contradiction"""
    while True:
        unm = np.flatnonzero(phi < 0)
        if unm.size == 0:
            return True
        cnt = C[unm].sum(axis=1)
        if (cnt == 0).any():
            return False
        forced = unm[cnt == 1]
        if forced.size == 0:
            return True
        for v in forced:
            if phi[v] >= 0:
                continue
            cands = np.flatnonzero(C[v])
            if cands.size != 1:
                return False
            w = cands[0]
            if phi[v] < 0 and C[:, w].sum() == 0:
                return False
            assign(C, phi, v, w, D)


class Budget(Exception):
    pass


def solve(C, phi, D, rng, st):
    if not propagate(C, phi, D):
        return None
    unm = np.flatnonzero(phi < 0)
    if unm.size == 0:
        return phi
    st['nodes'] += 1
    if time.time() > st['deadline']:
        raise Budget()
    cnt = C[unm].sum(axis=1)
    m = cnt.min()
    best = unm[cnt == m]
    v = int(best[rng.integers(best.size)])
    cands = np.flatnonzero(C[v])
    rng.shuffle(cands)
    for w in cands:
        C2 = C.copy()
        phi2 = phi.copy()
        assign(C2, phi2, v, int(w), D)
        res = solve(C2, phi2, D, rng, st)
        if res is not None:
            return res
    return None


def find_duality(q, seed, time_limit=600.0):
    H = gh.load(q)
    D, adj = gh.distances(H)
    D = D.astype(np.int16)
    n = D.shape[0]
    N = H.N
    colour = np.array([0] * N + [1] * N)
    C = (colour[:, None] != colour[None, :])
    phi = -np.ones(n, dtype=np.int64)
    rng = np.random.default_rng(seed)
    st = {'nodes': 0, 'deadline': time.time() + time_limit}
    res = solve(C, phi, D, rng, st)
    if res is None:
        return None, st['nodes'], D
    ok = bool((D[np.ix_(res, res)] == D).all())
    assert ok, 'not distance preserving'
    return res, st['nodes'], D


if __name__ == '__main__':
    q = int(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600.0
    t0 = time.time()
    phi, nodes, D = find_duality(q, seed, tl)
    if phi is None:
        print('no duality found', 'nodes', nodes, 'time', round(time.time() - t0, 1))
    else:
        np.save(out, phi)
        N = len(phi) // 2
        absolute = int(sum(1 for p in range(N) if D[p, phi[p]] == 1))
        print('duality found', 'nodes', nodes, 'time', round(time.time() - t0, 1),
              'points->lines', bool((phi[:N] >= N).all()), 'absolute(incident) points', absolute)
