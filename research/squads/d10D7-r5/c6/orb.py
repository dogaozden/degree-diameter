# Orbit structure of the order-91 group <g> on H(9) points; self-compatible orbits and orbit conflict graph.
import pickle, sys, time
import numpy as np
FN = '/home/user/degree-diameter/research/d10D7/hex/hex_q9.bin'
import struct
data = open(FN, 'rb').read()
q, N, _ = struct.unpack_from('<iii', data, 0)
LP = np.frombuffer(data, dtype='<i4', count=N*10, offset=12).reshape(N, 10).astype(np.int64).copy()
d = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r5/c6/grp.pkl', 'rb'))
perm = d['perm'].astype(np.int64)
# point -> lines
flat = LP.ravel(); lines_of = np.repeat(np.arange(N), 10)
o = np.argsort(flat, kind='stable'); PL = lines_of[o].reshape(N, 10)
assert np.all(np.bincount(flat, minlength=N) == 10)
allp = LP[PL]                      # N x 10 x 10
mask = allp != np.arange(N)[:, None, None]
NB = allp[mask].reshape(N, 90)
assert all(len(set(r)) == 90 for r in NB[:50].tolist())
# orbits of perm
orbit_of = -np.ones(N, np.int64); orbits = []
for p in range(N):
    if orbit_of[p] >= 0: continue
    cyc = []; x = p
    while True:
        cyc.append(x); orbit_of[x] = len(orbits); x = perm[x]
        if x == p: break
    orbits.append(cyc)
L = np.array([len(c) for c in orbits])
print('orbits', len(orbits), 'sizes', np.unique(L, return_counts=True))
M = len(orbits)
same = orbit_of[NB] == orbit_of[:, None]
bad = np.zeros(M, bool); bad[np.unique(orbit_of[np.nonzero(same.any(axis=1))[0]])] = True
print('self-conflicting orbits', int(bad.sum()), 'self-compatible', int((~bad).sum()))
CM = np.zeros((M, M), bool)
CM[orbit_of[:, None].repeat(90, 1), orbit_of[NB]] = True
np.fill_diagonal(CM, False)
good = np.nonzero(~bad)[0]
Cg = CM[np.ix_(good, good)]
comp = ~Cg; np.fill_diagonal(comp, False)
print('compatibility graph on', len(good), 'orbits, density', comp.sum() / (len(good)*(len(good)-1)))
deg = comp.sum(1)
print('compat degree min/mean/max', deg.min(), deg.mean(), deg.max())
pickle.dump({'orbits': orbits, 'orbit_of': orbit_of, 'good': good, 'comp': comp, 'NB': NB, 'PL': PL, 'LP': LP}, open('/home/user/degree-diameter/research/squads/d10D7-r5/c6/orb.pkl', 'wb'))
