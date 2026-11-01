import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers
from analyse import coset_nb_dp
def run(p, k, r, d, D, n, seed):
    G = Frob(p, k, r); N = G.N; h = (D - 1) // 2
    rng = np.random.default_rng(seed); jj = np.arange(N) % k
    res = []
    t0 = time.time()
    while len(res) < n and time.time() - t0 < 30:
        S = [0] + [int(x) for x in rng.choice(np.arange(1, N), size=d - 1, replace=False)]
        if len(set(s % k for s in S)) < 3: continue
        XA, XB = covers(G, S, D)
        hA = ~XA
        hc = np.bincount(jj[hA], minlength=k)
        res.append((int(hA.sum()), hc.tolist(), S))
    med = np.median([x[0] for x in res])
    return N, med, res
N, med, res = run(761, 19, 25, 4, 11, 40, 5)
print('k=19 (4,11) N', N, 'median holes A', med, 'size law', round(N*np.exp(-4*3**9/N),1))
N, med, res = run(21589, 7, 17486, 5, 11, 15, 1)
print('k=7 (5,11) N', N, 'median holes A', med)
best = sorted(res, key=lambda x: x[0])[0]
print('per-coset holes of best (k=7):', best[1], 'total', best[0])
N, med, res = run(21589, 7, 17486, 4, 11, 15, 2)
print('k=7 (4,11) N', N, 'median holes A', med)
