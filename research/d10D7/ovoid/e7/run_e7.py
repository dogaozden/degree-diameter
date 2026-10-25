import sys, time, numpy as np, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/d10D7/ovoid/e7')
from orb11 import *
t0 = time.time()
w = W(11)
print('loaded', round(time.time() - t0, 1), 'N', w.G.N, flush=True)
simple, roots = load_e7(11)
perms = [w.refl_perm(v) for v in simple]
print('perms', round(time.time() - t0, 1), flush=True)
lab = orbits_from_perms(w.G.N, perms)
sizes = np.bincount(lab)
print('orbits', len(sizes), 'sizes', sorted(sizes.tolist()), round(time.time() - t0, 1), flush=True)
members, S, A = sc_and_compat(w.G, lab)
print('self-compatible orbits', len(S), [int(sizes[o]) for o in S], flush=True)
if len(S):
    wgt, cl, done = best_union(members, S, A)
    print('best union', wgt, 'orbits', [int(sizes[o]) for o in cl], 'exact', done, flush=True)
    pts = sorted(int(p) for o in cl for p in members[o])
    open('/home/user/degree-diameter/research/d10D7/ovoid/e7/best_E7.txt', 'w').write('\n'.join(map(str, pts)) + '\n')
np.save('/home/user/degree-diameter/research/d10D7/ovoid/e7/lab_E7.npy', lab)
print('done', round(time.time() - t0, 1))
