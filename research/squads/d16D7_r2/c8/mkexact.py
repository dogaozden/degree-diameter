# Exact-cover instances on orbits.
# spreads (lines problem): columns = point-orbits, rows = line-orbit vertices, row covers the point-orbits of its 14 points.
# dual (points problem):   columns = line-orbits,  rows = point-orbit vertices, row covers the line-orbits of its 14 lines.
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from geo import build_PL, orbits_of
q, N, L, LP, X = load_hex()
gp = load_perm(D+'data/g13o61_pts.bin'); gl = load_perm(D+'data/g13o61_lines.bin')
orbit_p, orbs_p = orbits_of(gp); orbit_l, orbs_l = orbits_of(gl)
PL = build_PL(LP, N)
M, E, rep_p, nb_p = load_og(D+'og_pts.txt')
M2, E2, rep_l, nb_l = load_og(D+'og_lines.txt')
which = sys.argv[1]
if which == 'spread':   # lines problem
    rows = []
    for i in range(M2):
        pts = LP[rep_l[i]]
        cols = orbit_p[pts]
        assert len(set(cols.tolist())) == 14, 'row with repeated orbit'
        rows.append((i, cols.tolist()))
    ncol = len(orbs_p)
else:                   # points problem
    rows = []
    for i in range(M):
        lines = PL[rep_p[i]]
        cols = orbit_l[lines]
        assert len(set(cols.tolist())) == 14, 'row with repeated orbit'
        rows.append((i, cols.tolist()))
    ncol = len(orbs_l)
with open(f'exact_{which}.txt', 'w') as f:
    f.write(f'{len(rows)} {ncol}\n')
    for i, cols in rows:
        f.write(f'{i} ' + ' '.join(map(str, cols)) + '\n')
cnt = np.bincount(np.array([c for _, cs in rows for c in cs]), minlength=ncol)
print(which, 'rows', len(rows), 'cols', ncol, 'column degree', np.unique(cnt, return_counts=True))
