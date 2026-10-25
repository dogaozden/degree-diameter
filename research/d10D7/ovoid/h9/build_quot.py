# Orbit conflict graphs for the subgroup <g^E> of the order-91 element g of SL(3,9) acting on H(9) (squad r6 c4).
# E = 1: order 91 (730 orbits of 91); E = 13: order 7 (orbits of 7); E = 7: order 13 (orbits of 13).
# usage: build_quot.py E TAG SETFILE
# writes g{TAG}.bin (int32 n, s, m2; indptr[n+1]; indices[m2]; members[n*s]) and init_{TAG}.txt
# (orbit indices of the points of SETFILE, which must be a union of orbits).
import pickle, sys
import numpy as np
E = int(sys.argv[1]); TAG = sys.argv[2]; SETF = sys.argv[3]
R5 = '/home/user/degree-diameter/research/squads/d10D7-r5/c6/'
OUT = '/home/user/degree-diameter/research/squads/d10D7-r6/c4/'
d = pickle.load(open(R5 + 'orb.pkl', 'rb'))
gd = pickle.load(open(R5 + 'grp.pkl', 'rb'))
perm = np.asarray(gd['perm'], dtype=np.int64)
NB = np.asarray(d['NB'], dtype=np.int64)
del d
N = len(perm)
assert NB.shape == (N, 90)
p = np.arange(N, dtype=np.int64)
for _ in range(E):
    p = perm[p]
pl = p.tolist()
orbit_of = [-1] * N
orbits = []
for x0 in range(N):
    if orbit_of[x0] >= 0:
        continue
    cyc = []
    x = x0
    while True:
        cyc.append(x); orbit_of[x] = len(orbits); x = pl[x]
        if x == x0:
            break
    orbits.append(cyc)
orbit_of = np.array(orbit_of, dtype=np.int64)
M = len(orbits)
sizes = np.array([len(c) for c in orbits])
vals, cnts = np.unique(sizes, return_counts=True)
print('E', E, 'orbits', M, 'sizes', dict(zip(vals.tolist(), cnts.tolist())), flush=True)
assert len(vals) == 1
s = int(vals[0])
same = orbit_of[NB] == orbit_of[:, None]
bad = np.zeros(M, bool)
bad[np.unique(orbit_of[np.nonzero(same.any(axis=1))[0]])] = True
good = np.nonzero(~bad)[0]
n = len(good)
newid = -np.ones(M, np.int64); newid[good] = np.arange(n)
src = orbit_of[np.repeat(np.arange(N), 90)]
dst = orbit_of[NB.ravel()]
ok = (newid[src] >= 0) & (newid[dst] >= 0) & (src != dst)
a = newid[src[ok]]; b = newid[dst[ok]]
del src, dst, ok
key = np.unique(a * n + b)
A = key // n; Bv = key % n
deg = np.bincount(A, minlength=n)
indptr = np.zeros(n + 1, np.int64); indptr[1:] = np.cumsum(deg)
mem = np.array([orbits[g] for g in good], dtype=np.int32)
m2 = len(Bv)
print('good orbits', n, 'self-conflicting', M - n, 'degree min/mean/max', int(deg.min()), round(float(deg.mean()), 1), int(deg.max()), 'm2', m2, flush=True)
with open(OUT + 'g%s.bin' % TAG, 'wb') as f:
    np.array([n, s, m2], dtype='<i4').tofile(f)
    indptr.astype('<i4').tofile(f)
    Bv.astype('<i4').tofile(f)
    mem.astype('<i4').tofile(f)
ids = np.array(open(SETF).read().split(), dtype=np.int64)
o = np.unique(orbit_of[ids])
assert np.all(newid[o] >= 0), 'set uses a self-conflicting orbit'
tot = sum(len(orbits[x]) for x in o)
print('init set points', len(ids), 'orbits used', len(o), 'points in those orbits', tot, flush=True)
assert tot == len(ids), 'set is not a union of orbits'
with open(OUT + 'init_%s.txt' % TAG, 'w') as f:
    f.write('\n'.join(map(str, np.sort(newid[o]).tolist())) + '\n')
print('wrote', OUT + 'g%s.bin' % TAG, 'and', OUT + 'init_%s.txt' % TAG, flush=True)
