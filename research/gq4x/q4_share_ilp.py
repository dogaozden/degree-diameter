"""Degree q+2, diameter 4 from Q(4,q) with stand-ins: one copy z_a of each ovoid point a, and line copies whose
points may be stood in for by z_a. Constraint: every non-ovoid point on at most 1 copied line, every ovoid point
on at most 2 (one served by a, one by z_a). Exact maximum by ILP (HiGHS). Order 2(q+1)(q^2+1) + (q^2+1) + |M|.

python3 q4_share_ilp.py q SECONDS   -> builds the graph, checks it, writes graphs/q4_share_q{q}_n{n}.json
Run with PYTHONDONTWRITEBYTECODE=1 (imports research/gq4/gq_clones.py read-only).
"""
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'gq4'))
from gq_clones import q4, lib  # noqa: E402

q, secs = int(sys.argv[1]), float(sys.argv[2])
pts, lines, ovoid = q4(q)
n, m = len(pts), len(lines)
O = set(ovoid)
A = lil_matrix((n, m))
for j, L in enumerate(lines):
    for p in L:
        A[p, j] = 1
cap = np.array([2 if p in O else 1 for p in range(n)])
res = milp(-np.ones(m), constraints=[LinearConstraint(A.tocsr(), 0, cap)], integrality=np.ones(m),
           bounds=Bounds(0, 1), options={'time_limit': secs, 'disp': False})
x = np.round(res.x).astype(int)
M = [j for j in range(m) if x[j]]
print(f'q={q}: |M|={len(M)} status={res.message} bound={getattr(res, "mip_dual_bound", None)}')
# build: points 0..n-1, lines n..n+m-1, ovoid copies, line copies
on = [[] for _ in range(n)]
for j, L in enumerate(lines):
    for p in L:
        on[p].append(n + j)
edges = [(p, n + j) for j, L in enumerate(lines) for p in L]
v = n + m
z = {}
for a in sorted(O):
    z[a] = v
    edges += [(v, Lv) for Lv in on[a]]
    v += 1
used = set()
for j in M:
    y = v
    v += 1
    for p in lines[j]:
        s = p if p not in used else z[p]
        assert s not in used
        used.add(s)
        edges.append((s, y))
N = v
ok = lib.is_valid(N, edges, q + 2, 4)
print(f'n={N}, valid={ok}')
if ok:
    out = HERE / 'graphs' / f'q4_share_q{q}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{q+2}D4', 'value': N, 'output': [N, [list(e) for e in edges]]}))
    print('wrote', out)
