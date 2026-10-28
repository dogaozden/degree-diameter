"""Orbit quotient of the H(11) collinearity graph by a point-orbit partition (TAG_porb.bin, orbit id per point).
Only orbits of size SIZE are kept (so the ILS, which is unweighted, scores every orbit equally).
Admissible orbit: no neighbour of its representative lies in it. Writes CSR over admissible kept orbits:
TAG2_{n,off,nb,orb}.bin.   usage: quot_orb.py PORBTAG SIZE TAG2"""
import sys, numpy as np
ptag, SIZE, TAG2 = sys.argv[1], int(sys.argv[2]), sys.argv[3]
out = '/home/user/degree-diameter/research/squads/polylev/r2/e02/'
A = np.fromfile(out + 'pts11_nb.bin', dtype=np.int32).reshape(-1, 132).astype(np.int64)
N = A.shape[0]
orb = np.fromfile(out + ptag + '_porb.bin', dtype=np.int32).astype(np.int64)
no = orb.max() + 1
sizes = np.bincount(orb, minlength=no)
reps = np.full(no, -1, dtype=np.int64)
first = np.nonzero(np.r_[True, np.diff(np.sort(orb)) != 0])[0]  # placeholder (unused)
order = np.argsort(orb, kind='stable'); starts = np.r_[0, np.cumsum(sizes)[:-1]]
reps = order[starts]
own = (orb[A[reps]] == np.arange(no)[:, None]).any(axis=1)
keep = (sizes == SIZE) & ~own
ids = np.nonzero(keep)[0]
newid = -np.ones(no, dtype=np.int64); newid[ids] = np.arange(len(ids))
NB = orb[A[reps]]
nbrs = [set() for _ in range(no)]
for O in ids:
    for P in np.unique(NB[O]):
        if keep[P] and P != O:
            nbrs[O].add(int(P)); nbrs[int(P)].add(O)
off = [0]; nb = []
for O in ids:
    lst = sorted(newid[P] for P in nbrs[O]); nb.extend(lst); off.append(len(nb))
degs = np.diff(np.array(off)) if len(ids) else np.array([0])
np.array([len(ids)], dtype=np.int32).tofile(out + TAG2 + '_n.bin')
np.array(off, dtype=np.int32).tofile(out + TAG2 + '_off.bin')
np.array(nb, dtype=np.int32).tofile(out + TAG2 + '_nb.bin')
np.array(ids, dtype=np.int32).tofile(out + TAG2 + '_orb.bin')
np.array(orb, dtype=np.int32).tofile(out + TAG2 + '_porb.bin')
print('size-%d orbits %d, admissible kept %d, quotient degree min/mean/max %d %.1f %d' % (SIZE, int((sizes == SIZE).sum()), len(ids), degs.min(), degs.mean(), degs.max()), flush=True)
