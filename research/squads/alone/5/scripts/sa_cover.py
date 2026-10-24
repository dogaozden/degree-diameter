# Can 16 B-vertices radius-3 dominate A? Anneal the cover cost alone from random starts.
import sys, random, numpy as np
seed, iters, T0, T1 = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
rnd = random.Random(seed)
C = np.load('C3.npy'); nB = C.shape[0]
cen = rnd.sample(range(nB), 16)
cnt = C[cen].sum(axis=0).astype(np.int32)
cost = int((cnt == 0).sum()); best = cost
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / iters)
    i = rnd.randrange(16); new = rnd.randrange(nB)
    if new in cen: continue
    nc_arr = cnt - C[cen[i]] + C[new]
    nc = int((nc_arr == 0).sum()); d = nc - cost
    if d <= 0 or rnd.random() < np.exp(-d / T):
        cen[i] = new; cnt = nc_arr.astype(np.int32); cost = nc; best = min(best, cost)
        if cost == 0: break
print('seed', seed, 'final', cost, 'best', best, 'iters', it, flush=True)
if cost == 0: print('COVER', sorted(cen))
