"""Orbit quotient of the H(11) collinearity graph by a semiregular point permutation g (a .pperm file).
Orbit O is admissible if no two of its points are collinear; admissible orbits O, P conflict if some point of O is
collinear with some point of P. Writes CSR graph over admissible orbits: TAG_{n,off,nb,orb}.bin, plus
TAG_porb.bin (orbit id of every point).  usage: quot.py PPERM TAG"""
import sys, numpy as np
PPERM, TAG = sys.argv[1], sys.argv[2]
out = '/home/user/degree-diameter/research/squads/polylev/r2/e02/'
A = np.fromfile(out + 'pts11_nb.bin', dtype=np.int32).reshape(-1, 132).astype(np.int64)
N = A.shape[0]
perm = np.fromfile(PPERM, dtype=np.int32).astype(np.int64)
assert perm.shape[0] == N and np.array_equal(np.sort(perm), np.arange(N)), 'not a permutation'
# automorphism check: image of the neighbour set of x is the neighbour set of image of x
B = np.sort(perm[A], axis=1)
assert np.array_equal(B, A[perm]), 'not a collineation'
# orbits = cycles of perm
orb = -np.ones(N, dtype=np.int64)
reps = []
for x in range(N):
    if orb[x] >= 0: continue
    k = len(reps); reps.append(x)
    y = x
    while orb[y] < 0:
        orb[y] = k; y = perm[y]
no = len(reps)
sizes = np.bincount(orb)
print('orbits', no, 'orbit sizes', np.unique(sizes, return_counts=True), flush=True)
reps = np.array(reps)
# admissible: no neighbour of the representative lies in its own orbit (group-invariance covers the whole orbit)
own = (orb[A[reps]] == np.arange(no)[:, None]).any(axis=1)
adm = ~own
ids = np.nonzero(adm)[0]
newid = -np.ones(no, dtype=np.int64); newid[ids] = np.arange(len(ids))
nbrs = [set() for _ in range(no)]
NB = orb[A[reps]]                           # no x 132 orbit ids of neighbours of the representatives
for O in range(no):
    if not adm[O]: continue
    for P in np.unique(NB[O]):
        if adm[P] and P != O:
            nbrs[O].add(int(P)); nbrs[int(P)].add(O)
off = [0]; nb = []
for O in ids:
    lst = sorted(newid[P] for P in nbrs[O])
    nb.extend(lst); off.append(len(nb))
degs = np.diff(np.array(off))
np.array([len(ids)], dtype=np.int32).tofile(out + TAG + '_n.bin')
np.array(off, dtype=np.int32).tofile(out + TAG + '_off.bin')
np.array(nb, dtype=np.int32).tofile(out + TAG + '_nb.bin')
np.array(ids, dtype=np.int32).tofile(out + TAG + '_orb.bin')
orb.astype(np.int32).tofile(out + TAG + '_porb.bin')
print('admissible orbits', len(ids), 'of', no, '| quotient degree min/mean/max', degs.min(), round(degs.mean(), 1), degs.max(), flush=True)
