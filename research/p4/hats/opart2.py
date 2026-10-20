"""Delorme doubling on Q(4,q) with an ovoid O (single level, plus one optional second level).

A0 = O + M, where M is a set of lines whose non-ovoid points are pairwise disjoint (lines may share ovoid points).
Optionally A1 = {o} for an ovoid point o with all q+1 lines through o in M (Delorme's nested doubling, +2).
Order 2(q+1)(q^2+1) + (q^2+1) + |M| (+2).

python3 opart2.py q SECONDS [pencil]      pencil=1 forces the full pencil at ovoid[0] and adds level 2
"""
import json
import sys
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from lift import ROOT, lib, gq_edges
from gq_clones import q4

sys.path.insert(0, str(ROOT / 'research' / 'p4' / 'd6'))
import lift as _unused  # noqa: E402,F401  (our own lift module; d6's is loaded below by path)
import importlib.util  # noqa: E402

spec = importlib.util.spec_from_file_location('d6lift', ROOT / 'research' / 'p4' / 'd6' / 'lift.py')
d6lift = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d6lift)

q, secs = int(sys.argv[1]), float(sys.argv[2])
pencil = len(sys.argv) > 3 and sys.argv[3] == '1'
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
lb = np.zeros(m)
o = ovoid[0]
if pencil:
    for j, L in enumerate(lines):
        if o in L:
            lb[j] = 1
t = time.time()
res = milp(-np.ones(m), constraints=[LinearConstraint(A.tocsr(), 0, 1)], integrality=np.ones(m),
           bounds=Bounds(lb, 1), options={'time_limit': secs, 'disp': False})
x = np.round(res.x).astype(int)
M = [j for j in range(m) if x[j]]
print(f'q={q} pencil={pencil}: lines={len(M)} (max {q*q+1}) status={res.message} '
      f'bound={getattr(res, "mip_dual_bound", None)} {time.time()-t:.1f}s', flush=True)
adj = [[] for _ in range(n + m)]
for u, v in gq_edges(n, lines):
    adj[u].append(v)
    adj[v].append(u)
lev = [-1] * (n + m)
for p in O:
    lev[p] = 0
for j in M:
    lev[n + j] = 0
if pencil:
    lev[o] = 1
N, H, _ = d6lift.build(n + m, adj, lev)
ok = lib.is_valid(N, H, q + 2, 4)
print(f'order {N}, valid(D=4, Delta={q+2}) {ok}')
if ok:
    out = ROOT / 'research' / 'p4' / 'hats' / 'graphs' / f'opart_q{q}{"_pencil" if pencil else ""}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{q+2}D4', 'value': N, 'output': [N, [list(e) for e in H]],
                               'lines': M, 'ovoid': sorted(O)}))
    print('wrote', out)
