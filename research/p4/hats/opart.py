"""Q(4,q) with an ovoid O: find lines whose non-ovoid points are pairwise disjoint (an "O-partial spread": lines may
share an ovoid point). With C = O-points-used + those lines, the lift has degree q+2 and diameter 4.
Maximum is q^2+1 (exact partition of the q(q^2+1) non-ovoid points).

python3 opart.py q SECONDS
"""
import json
import sys
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from lift import ROOT, lib, gq_edges, lift, star_forest, max_degree
from gq_clones import q4

q, secs = int(sys.argv[1]), float(sys.argv[2])
pts, lines, ovoid = q4(q)
n, m = len(pts), len(lines)
O = set(ovoid)
non = [p for p in range(n) if p not in O]
row = {p: i for i, p in enumerate(non)}
A = lil_matrix((len(non), m))
for j, L in enumerate(lines):
    for p in L:
        if p not in O:
            A[row[p], j] = 1
t = time.time()
res = milp(-np.ones(m), constraints=[LinearConstraint(A.tocsr(), 0, 1)], integrality=np.ones(m),
           bounds=Bounds(0, 1), options={'time_limit': secs, 'disp': False})
x = np.round(res.x).astype(int)
M = [j for j in range(m) if x[j]]
print(f'q={q}: lines={len(M)} (max {q*q+1}) status={res.message} bound={getattr(res, "mip_dual_bound", None)} '
      f'{time.time()-t:.1f}s')
# C = all ovoid points + chosen lines (ovoid points not on a chosen line are isolated: plain copies)
C = sorted(O) + [n + j for j in M]
E = gq_edges(n, lines)
assert star_forest(n + m, E, C)
N, H = lift(n + m, E, C)
d, _ = max_degree(N, H)
ok = lib.is_valid(N, H, q + 2, 4)
print(f'order {N}, max degree {d}, valid(D=4, Delta={q+2}) {ok}')
if ok:
    out = ROOT / 'research' / 'p4' / 'hats' / 'graphs' / f'opart_q{q}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{q+2}D4', 'value': N, 'output': [N, [list(e) for e in H]]}))
    print('wrote', out)
