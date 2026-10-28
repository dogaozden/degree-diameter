"""Orbit quotient of the point-collinearity graph of H(8) by a semiregular permutation (cycles = orbits).
usage: build_quot.py PERM.pperm PREFIX   -> PREFIX_{n,off,nb,orb,rep,size}.bin (CSR over admissible orbits, the
layout used by r1/c12/mkquot2.py and mis2). Admissible: no two points of the orbit collinear."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q8.bin')
perm = np.fromfile(sys.argv[1], dtype=np.int32).astype(np.int64); prefix = sys.argv[2]
N = H.N; assert len(perm) == N and (np.sort(perm) == np.arange(N)).all()
orb = -np.ones(N, dtype=np.int64); sizes = []; no = 0
for s in range(N):
    if orb[s] >= 0: continue
    x, c = s, 0
    while orb[x] < 0: orb[x] = no; x = perm[x]; c += 1
    sizes.append(c); no += 1
sizes = np.array(sizes)
rep = np.full(no, -1)
for v in range(N):
    if rep[orb[v]] < 0: rep[orb[v]] = v
adm = np.ones(no, dtype=bool); nbrs = [set() for _ in range(no)]
# collinear neighbours of the representative (q(q+1)=72 points), via lines through it
for O in range(no):
    r = rep[O]
    for l in H.PL[r]:
        for y in H.lines[l]:
            if y == r: continue
            if orb[y] == O: adm[O] = False
            else: nbrs[O].add(int(orb[y]))
# symmetrise (collinearity is symmetric; the rep-based neighbourhoods of an orbit are its full neighbourhood
# because the group preserves collinearity)
for O in range(no):
    for P in list(nbrs[O]): nbrs[P].add(O)
ids = np.nonzero(adm)[0]
newid = -np.ones(no, dtype=np.int64); newid[ids] = np.arange(len(ids))
off = [0]; nb = []
for O in ids:
    lst = sorted(int(newid[P]) for P in nbrs[O] if adm[P]); nb.extend(lst); off.append(len(nb))
np.array([len(ids)], dtype=np.int32).tofile(prefix + '_n.bin')
np.array(off, dtype=np.int32).tofile(prefix + '_off.bin')
np.array(nb, dtype=np.int32).tofile(prefix + '_nb.bin')
np.array(ids, dtype=np.int32).tofile(prefix + '_orb.bin')
np.array(rep, dtype=np.int32).tofile(prefix + '_rep.bin')
np.array(orb, dtype=np.int32).tofile(prefix + '_porb.bin')
np.array(sizes, dtype=np.int32).tofile(prefix + '_size.bin')
degs = np.diff(np.array(off))
print('orbits', no, 'size set', sorted(set(sizes.tolist())), 'admissible', len(ids), 'deg min/mean/max', degs.min(), degs.mean(), degs.max(), flush=True)
