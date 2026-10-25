import sys, random, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import lns
from lns import N, PTS, LOF, read_sol, cover, lns_step, neighbourhood
S0 = read_sol('k10_orbit_38.sol'); F = S0['F']; H = S0['hubadj']; sig0 = S0['sig']
isfree = np.zeros(N, bool); isfree[F] = True
nonfree = np.nonzero(~isfree)[0]
sinv = np.empty(N, np.int64); sinv[sig0] = np.arange(N)
p = F[3]; t = 229
rel = set(np.nonzero(lns.PM[p] & ~isfree)[0].tolist()) | set(sinv[LOF[t]].tolist()) | {t}
rel = [x for x in rel if not isfree[x]]
rng = random.Random(7)
t0 = time.time(); 
for _ in range(20): cover(F, sig0, H)
print('cover time %.4f' % ((time.time() - t0) / 20))
for trial in range(300):
    s = sig0.copy(); x, y = rng.sample(rel, 2)
    s[x], s[y] = s[y], s[x]
    c = cover(F, s, H)
    if 10 <= c <= 30: break
print('kick', x, y, 'cost', c)
for S in ([x, y], [x, y] + rng.sample(rel, 8)):
    S = [int(z) for z in S]
    t0 = time.time()
    new, info = lns_step(F, s, H, S, 10, 3, 1)
    print('|S|', len(S), 'info', info, 'time %.1f' % (time.time() - t0), end=' ')
    if new is not None:
        print('exact after', cover(F, new, H), 'changed', int((new != s).sum()))
    else: print()
# plain 2-swap descent on touched+rel with exact cover
