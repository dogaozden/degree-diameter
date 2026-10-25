import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import numpy as np
import lns
from lns import PM, LOF, N
S = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S['F']; sig0 = S['sig']; hub = S['hubadj']
print('F', F, 'cover10', lns.cover(F, sig0, hub))
keep = [i for i in range(len(F)) if F[i] != 65]
F9 = [F[i] for i in keep]; hub9 = hub[np.ix_(keep, keep)]
print('F9', F9, 'cover9 (no swap)', lns.cover(F9, sig0, hub9))
crowd = {x: int(sum(PM[x, y] for y in F if y != x)) for x in F}
print('collinear counts in 10-set', crowd)
def swap(sig, p, l):
    s = sig.copy(); sinv = np.empty(N, np.int64); sinv[s] = np.arange(N)
    o = sinv[l]; t = s[p]; s[p] = l; s[o] = t
    return s, o
def hub_ext(h, k):
    H = np.zeros((k, k), bool); H[:h.shape[0], :h.shape[1]] = h; return H
t0 = time.time()
single = []
for p in range(N):
    if p in F9 or p == 65: continue
    for l in LOF[p]:
        if l in sig0[F9]: continue
        s, o = swap(sig0, p, l)
        if o in F9: continue
        if any(PM[p, x] for x in F9) and sum(PM[p, x] for x in F9) > 2: continue
        c = lns.cover(F9 + [p], s, hub_ext(hub9, len(F9) + 1))
        single.append((c, p, int(l)))
print('single screen time', round(time.time() - t0, 1), 'n', len(single))
single.sort()
print('best singles (10-flag candidates, no hub edges for new flag):', single[:15])
np.save('/home/user/degree-diameter/research/squads/d10D5/r4/c5/single.npy', np.array(single))
