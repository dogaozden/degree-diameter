"""Find a Hermitian spread of H(5) via a hyperplane with elliptic section; write spread.npy."""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import numpy as np
from hexlib import load
from itertools import product
q = 5
N, LP, PL, coord = load(q)
C = coord.astype(np.int64) % q
L = LP.shape[0]
print('N', N, 'L', L, 'coord sample', C[:3].tolist())
rng = np.random.default_rng(1)
# opposite test via incidence-graph distance computed by BFS on lines is costly; use hyperplane search first
best = None
for trial in range(4000):
    f = rng.integers(0, q, size=7)
    if not f.any():
        continue
    vals = (C @ f) % q
    inH = vals == 0
    # lines fully inside hyperplane
    full = inH[LP].all(axis=1)
    cnt = int(full.sum())
    if cnt == q**3 + 1:
        best = (f.copy(), np.where(full)[0])
        print('found hyperplane', f.tolist(), 'lines inside', cnt, 'trial', trial)
        break
if best is None:
    print('no elliptic hyperplane found'); sys.exit(1)
f, S = best
np.save('spread_lines.npy', S)
np.save('spread_f.npy', f)
# verify pairwise opposite: lines in S share no point and every pair at incidence distance 6
Sp = [set(LP[l].tolist()) for l in S]
pts_cov = set().union(*Sp)
print('spread lines', len(S), 'pairwise disjoint points:', len(pts_cov) == len(S) * (q + 1))
# distance check: two lines are opposite iff no point of one is collinear with a point of other... use BFS on lines
from hexlib import dist_from_point
ok = True
for a in S[:20]:
    p = LP[a][0]
    dp, dl = dist_from_point(p, LP, PL)
    # line a has distance 1 from p; distance from a to other spread lines: min over points of l
    for b in S:
        if b == a: continue
        if dl[b] <= 4 and dl[b] != 99:
            ok = False
print('spread check (sample of 20 lines, lines at distance <=4 from a point of a):', ok)
