#!/usr/bin/env python3
"""check_points.py HEX COLOURFILE: independent check of point classes (card e14, D = 9).

For each colour c: the points coloured c lie on Q(6,q) (Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0) and every point p has a
class-c point equal or collinear to p (collinear = on a common line of H(q), computed from the line list directly).
Prints the number of dominating classes (pairwise disjoint by construction: one colour per point).
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

H = Hex(sys.argv[1])
col = np.fromfile(sys.argv[2], dtype=np.int32).astype(np.int64)
q, N = H.q, H.N
A, M, Ng = H.ADD, H.MUL, H.NEG
X = H.coord
# Q(x) = x0x4 + x1x5 + x2x6 - x3^2
Qv = A[A[A[M[X[:, 0], X[:, 4]], M[X[:, 1], X[:, 5]]], M[X[:, 2], X[:, 6]]], Ng[M[X[:, 3], X[:, 3]]]]
assert (Qv == 0).all(), 'a point is not on Q(6,q)'
# collinearity: x ~ p iff x on a line through p (computed from the line list)
coll = [set() for _ in range(N)]
for l in range(H.L):
    pts = H.lines[l]
    for p in pts:
        coll[p].update(int(x) for x in pts)
ok = 0
best = []
for c in sorted(set(col[col >= 0].tolist())):
    mem = set(np.where(col == c)[0].tolist())
    dom = all((p in mem) or bool(coll[p] & mem) for p in range(N))
    if dom:
        ok += 1
    best.append((c, dom, len(mem)))
print(f'q={q}: colours {len(best)}, dominating point classes {ok}; class sizes min {min(s for _,_,s in best)} '
      f'max {max(s for _,_,s in best)}')
