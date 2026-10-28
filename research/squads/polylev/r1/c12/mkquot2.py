"""Quotient graphs of the point / line graphs by the order-73 Singer group (semiregular, 513 orbits of 73).
Admissible orbit = its representative has no neighbour in the same orbit. Writes CSR graphs over admissible orbits."""
import sys, numpy as np
side = sys.argv[1]; tag = sys.argv[3]
A = np.fromfile(f'{side}_adj.bin', dtype=np.int32).reshape(-1, 72)
orb = np.fromfile(sys.argv[2], dtype=np.int32)
n = A.shape[0]
no = orb.max() + 1
rep = np.full(no, -1)
for v in range(n):
    if rep[orb[v]] < 0: rep[orb[v]] = v
adm = np.ones(no, dtype=bool)
nbrs = [set() for _ in range(no)]
for O in range(no):
    r = rep[O]
    for u in A[r]:
        if orb[u] == O: adm[O] = False
        else: nbrs[O].add(int(orb[u]))
# symmetrise (should already be symmetric)
for O in range(no):
    for P in list(nbrs[O]):
        nbrs[P].add(O)
ids = np.nonzero(adm)[0]
newid = -np.ones(no, dtype=np.int64); newid[ids] = np.arange(len(ids))
off = [0]; nb = []
for O in ids:
    lst = sorted(newid[P] for P in nbrs[O] if adm[P])
    nb.extend(lst); off.append(len(nb))
np.array([len(ids)], dtype=np.int32).tofile(f'{tag}_n.bin')
np.array(off, dtype=np.int32).tofile(f'{tag}_off.bin')
np.array(nb, dtype=np.int32).tofile(f'{tag}_nb.bin')
np.array(ids, dtype=np.int32).tofile(f'{tag}_orb.bin')
np.array(rep, dtype=np.int32).tofile(f'{tag}_rep.bin')
np.array(orbsz:=np.bincount(orb), dtype=np.int32).tofile(f'{tag}_size.bin')
degs = np.diff(np.array(off))
print(side, 'orbits', no, 'admissible', len(ids), 'quotient degree min/mean/max', degs.min() if len(degs) else 0, degs.mean() if len(degs) else 0, degs.max() if len(degs) else 0)
