"""Random S: min total cost, split by whether z=(52,0) is reached on side A and on side B."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *
m, k, r, samples, z = map(int, sys.argv[1:6]); seed = 11
T = meta_table(m, k, r); Sinv = inverses(T); N = T.shape[0]
zi = z  # index of element (a,j) = a + m*j is passed directly
rng = np.random.default_rng(seed)
res = {}
for it in range(samples):
    S = np.array([0] + list(rng.choice(np.arange(1, N), 3, replace=False)))
    TA = prodset(T, Sinv[S], S); TB = prodset(T, S, Sinv[S])
    PA = np.array([0]); PB = np.array([0])
    for _ in range(4):
        PA = prodset(T, PA, TA); PB = prodset(T, PB, TB)
    fa = N - len(PA); fb = N - len(PB)
    inA = zi in set(PA.tolist()); inB = zi in set(PB.tolist())
    key = (inA, inB)
    cur = res.setdefault(key, [10**9, 0])
    cur[0] = min(cur[0], fa + fb); cur[1] += 1
for key, v in sorted(res.items()):
    print("z reached A=%s B=%s : samples %d, min cost seen %d" % (key[0], key[1], v[1], v[0]))
