# c2: T_m-orbit compatibility graph and randomized clique search.
import numpy as np, sys, time, pickle
from gf import nonorth, NP
def orbit_graph(m, seed=0):
    Mp = NP // m                      # orbit residues mod Mp; orbit of r = {r + j*Mp}
    R = np.arange(Mp, dtype=np.int64)
    selfok = np.ones(Mp, dtype=bool)
    for j in range(1, m):
        selfok &= nonorth(R, (R + j * Mp) % NP)
    SC = np.nonzero(selfok)[0]
    n = len(SC)
    A = np.zeros((n, n), dtype=bool)
    ks = np.arange(m, dtype=np.int64) * Mp
    for i, r in enumerate(SC):
        # compat of orbit r with orbit s: nonorth(r, s + k Mp) for all k
        vals = nonorth(np.full((n, m), r, dtype=np.int64), (SC[:, None] + ks[None, :]) % NP)
        A[i] = vals.all(axis=1)
    np.fill_diagonal(A, False)
    return SC, A

def greedy_clique(A, rng, iters=200):
    n = A.shape[0]; best = []
    if n == 0: return best
    deg = A.sum(1)
    for it in range(iters):
        C = np.ones(n, dtype=bool); cl = []
        v = rng.integers(n) if it % 2 else int(np.argmax(deg + rng.random(n)))
        while True:
            cl.append(v); C &= A[v]; C[v] = False
            idx = np.nonzero(C)[0]
            if len(idx) == 0: break
            # pick candidate with most neighbours inside C (random tie break), sample a few for speed
            sub = idx if len(idx) <= 300 else rng.choice(idx, 300, replace=False)
            cnt = A[np.ix_(sub, idx)].sum(1) + rng.random(len(sub))
            v = int(sub[np.argmax(cnt)])
        if len(cl) > len(best): best = cl[:]
    return best

if __name__ == '__main__':
    m = int(sys.argv[1]); iters = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    t0 = time.time()
    SC, A = orbit_graph(m)
    print('m', m, 'orbits', NP // m, 'self-compatible', len(SC), 'edge density', A.sum() / max(1, len(SC) * (len(SC) - 1)), 'time %.1f' % (time.time() - t0), flush=True)
    rng = np.random.default_rng(1)
    cl = greedy_clique(A, rng, iters)
    print('greedy clique (orbits)', len(cl), 'points', len(cl) * m, flush=True)
    pts = sorted(int((SC[c] + j * (NP // m)) % NP) for c in cl for j in range(m))
    np.save('best_T%d_L.npy' % m, np.array(pts, dtype=np.int64))
    print('saved', len(pts))
