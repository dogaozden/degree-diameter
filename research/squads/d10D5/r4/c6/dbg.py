import sys, random, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import lns
from lns import N, PTS, LOF, read_sol, cover, lns_step, neighbourhood
S0 = read_sol('k10_orbit_38.sol'); F = S0['F']; H = S0['hubadj']; sig0 = S0['sig']
isfree = np.zeros(N, bool); isfree[F] = True
nonfree = np.nonzero(~isfree)[0]
rng = random.Random(7)
sinv = np.empty(N, np.int64); sinv[sig0] = np.arange(N)
p = F[3]; t = 229
rel = set(np.nonzero(lns.PM[p] & ~isfree)[0].tolist()) | set(sinv[LOF[t]].tolist()) | {t}
rel = [x for x in rel if not isfree[x]]
# one swap that gives cost ~14
for trial in range(200):
    s = sig0.copy(); x, y = rng.sample(rel, 2)
    s[x], s[y] = s[y], s[x]
    c = cover(F, s, H)
    if 10 <= c <= 30: break
print('kick', x, y, 'cost', c)
S = list(dict.fromkeys([x, y] + neighbourhood(F, s, cover(F, s, H, listing=True)[1], 90, rng)))
print('|S|', len(S), 'orig in S?', x in S, y in S)
for secs in (5, 20):
    t0 = time.time()
    new, info = lns_step(F, s, H, S, secs, 3, 1)
    print('secs', secs, 'info', info, 'time %.1f' % (time.time() - t0))
    if new is not None:
        print('exact after', cover(F, new, H), 'changed', int((new != s).sum()))
# check: is the original sigma (sig0) a feasible assignment of the model? exact cost of sig0 restricted:
print('exact sig0', cover(F, sig0, H))
