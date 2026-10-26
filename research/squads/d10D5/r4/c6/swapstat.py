import sys, random, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import lns
from lns import N, PTS, LOF, read_sol, cover
S0 = read_sol('k10_orbit_38.sol'); F = S0['F']; H = S0['hubadj']; sig0 = S0['sig']
isfree = np.zeros(N, bool); isfree[F] = True
nonfree = np.nonzero(~isfree)[0]
rng = random.Random(5)
sinv = np.empty(N, np.int64); sinv[sig0] = np.arange(N)
p = F[3]; t = 229
rel = set(np.nonzero(lns.PM[p] & ~isfree)[0].tolist()) | set(sinv[LOF[t]].tolist()) | {t}
rel = [x for x in rel if not isfree[x]]
print('rel size', len(rel))
def trial(pool_fn, n=200):
    vals = []
    for _ in range(n):
        s = sig0.copy(); x, y = pool_fn()
        s[x], s[y] = s[y], s[x]
        vals.append(cover(F, s, H))
    return np.percentile(vals, [0, 10, 50, 90, 100])
print('random pair', trial(lambda: rng.sample(list(nonfree), 2)))
print('rel-rel pair', trial(lambda: rng.sample(rel, 2)))
print('rel-random', trial(lambda: (rng.choice(rel), rng.choice(list(nonfree)))))
print('collinear-with-p pair', trial(lambda: rng.sample(rel[:], 2)))
# cost of sigma swap within the nbhd of lines through p
w = [int(sinv[L]) for L in LOF[p] if not isfree[sinv[L]]]
print('w-line preimages', len(w))
