import time, numpy as np
from hx import *
G = geo(); R = np.load('roots13.npy')
t = time.time()
E6 = ([(0,1),(1,2),(2,3),(3,4),(2,5)], 6)
B = subsystem(R, Q, E6[0], E6[1], seed=1, tries=300)
print('E6 basis', B is not None, round(time.time()-t,1), flush=True)
perms = refl_perms(B)
members, counts = orbits_of(perms)
print('orbits', len(members), 'sizes', sorted(np.bincount(np.zeros(1,int))) if False else sorted(counts.tolist())[:10], '...', sorted(counts.tolist())[-5:], round(time.time()-t,1), flush=True)
S = set(open('/home/user/degree-diameter/research/d10D7/sets/P13_E7sub_E6_792.txt').read().split())
S = set(int(x) for x in S)
pt2orb = np.empty(G.N, int)
for o, m in enumerate(members): pt2orb[m] = o
cnt = {}
for p in S: cnt[pt2orb[p]] = cnt.get(pt2orb[p], 0) + 1
print('792 set touches orbits', {int(o): (c, int(counts[o])) for o, c in cnt.items()}, flush=True)
