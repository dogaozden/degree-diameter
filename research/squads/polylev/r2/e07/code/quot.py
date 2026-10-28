"""Orbit quotient of the H(7) point-collinearity graph by a semiregular permutation group.
usage: quot.py HEXBIN PERMFILE PREFIX
Writes PREFIX_{n,off,nb,orb,rep,size}.bin (CSR over admissible orbits, same layout as r1/c12/mkquot2.py).
Admissible orbit: no two of its points are collinear (checked on the representative, which suffices because
the group acts by collinearity-preserving permutations). Orbits are the cycles of PERMFILE (semiregular)."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

hexbin, permfile, prefix = sys.argv[1], sys.argv[2], sys.argv[3]
H = Hex(hexbin)
N = H.N
# collinearity neighbours: all points on a common line (56 for q=7)
nbr = np.zeros((N, H.q * (H.q + 1)), dtype=np.int64)
cnt = np.zeros(N, dtype=np.int64)
for x in range(N):
    s = []
    for l in H.PL[x]:
        s.extend(int(y) for y in H.lines[l] if y != x)
    s = sorted(set(s))
    assert len(s) == H.q * (H.q + 1), (x, len(s))
    nbr[x] = s
perm = np.fromfile(permfile, dtype=np.int32).astype(np.int64)
assert len(perm) == N and sorted(perm.tolist()) == list(range(N))
# cycles of perm = orbits (semiregular case: all cycles of one length)
orb = -np.ones(N, dtype=np.int64)
no = 0
sizes = []
for s in range(N):
    if orb[s] >= 0:
        continue
    x, c = s, 0
    while orb[x] < 0:
        orb[x] = no
        x = perm[x]
        c += 1
    sizes.append(c)
    no += 1
sizes = np.array(sizes)
print('orbits', no, 'orbit size values', np.unique(sizes, return_counts=True), flush=True)
rep = np.full(no, -1, dtype=np.int64)
for v in range(N):
    if rep[orb[v]] < 0:
        rep[orb[v]] = v
# admissibility and quotient adjacency, checked on the representative
adm = np.ones(no, dtype=bool)
nbrs = [set() for _ in range(no)]
for O in range(no):
    r = rep[O]
    for u in nbr[r]:
        if orb[u] == O:
            adm[O] = False
        else:
            nbrs[O].add(int(orb[u]))
# symmetry check on a sample of orbits
for O in range(no):
    for P in nbrs[O]:
        assert O in nbrs[P], 'asymmetric quotient'
# invariance check: every point of an orbit has the same orbit-neighbour pattern
for trial in range(2000):
    v = np.random.default_rng(trial).integers(N)
    O = orb[v]
    if O is None:
        continue
    seen = set(int(orb[u]) for u in nbr[v])
    assert seen == nbrs[O] | ({O} if not adm[O] else set()) or (not adm[O]) or seen == nbrs[O], 'not invariant'
ids = np.nonzero(adm)[0]
newid = -np.ones(no, dtype=np.int64)
newid[ids] = np.arange(len(ids))
off = [0]
nb = []
for O in ids:
    lst = sorted(int(newid[P]) for P in nbrs[O] if adm[P])
    nb.extend(lst)
    off.append(len(nb))
np.array([len(ids)], dtype=np.int32).tofile(prefix + '_n.bin')
np.array(off, dtype=np.int32).tofile(prefix + '_off.bin')
np.array(nb, dtype=np.int32).tofile(prefix + '_nb.bin')
np.array(ids, dtype=np.int32).tofile(prefix + '_orb.bin')
np.array(rep, dtype=np.int32).tofile(prefix + '_rep.bin')
np.array(sizes, dtype=np.int32).tofile(prefix + '_size.bin')
np.array(orb, dtype=np.int32).tofile(prefix + '_orbof.bin')
degs = np.diff(np.array(off))
print('admissible', len(ids), 'of', no, 'quotient degree min/mean/max', degs.min(), round(degs.mean(), 2), degs.max(), flush=True)
