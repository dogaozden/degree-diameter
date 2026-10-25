"""Diagnose uncovered (line, level) pairs of a base file (cyclic Z_m lift, D = 8) from one source point.
usage: python3 diag.py q base.txt src_point"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, dist_from_point
q, fn, src = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
N, LP, PL, coord = load(q)
with open(fn) as f:
    nA, nB, m = map(int, f.readline().split())
E = np.loadtxt(fn, skiprows=1, dtype=np.int64)
a, b, v = E[:, 0], E[:, 1], E[:, 2] % m
R = np.zeros((N, m), dtype=bool); R[src, 0] = True   # points at level-tracking
Rl = None
# walk of length 7 from point src: alternate point->line (+v) and line->point (-v)
Ap = R
for step in range(7):
    if step % 2 == 0:       # point -> line
        Bl = np.zeros((N, m), dtype=bool)
        for x in range(m):   # rows of Ap with level x
            pass
        idx = np.nonzero(Ap[a])            # (edge index, level) pairs
        ei, lev = idx
        np.logical_or.at(Bl, (b[ei], (lev + v[ei]) % m), True)
        Ap = Bl
    else:                    # line -> point
        Pn = np.zeros((N, m), dtype=bool)
        idx = np.nonzero(Ap[b])
        ei, lev = idx
        np.logical_or.at(Pn, (a[ei], (lev - v[ei]) % m), True)
        Ap = Pn
unc = ~Ap                                # after 7 steps we are on lines
dp, dl = dist_from_point(src, LP, PL)
cnt = unc.sum(axis=1)
for d in range(1, 7):
    sel = dl == d
    if sel.sum():
        print(f'hex distance {d}: lines {sel.sum()}, uncovered pairs {cnt[sel].sum()}, lines with some uncovered {(cnt[sel] > 0).sum()}')
print('total uncovered for this source', cnt.sum())
