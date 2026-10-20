"""Best Delorme doubling of a GQ(q,q) incidence graph at degree q+2, by ILP (HiGHS via scipy).

Single level A0 = C: the induced subgraph on C must be a star forest (D = 4 condition) and every vertex outside C has
at most one neighbour in C. Level 2: A1 = centres of full stars (all q+1 neighbours in C), +2 each.
Gain |A0| + 2|A1|; order 2(q+1)(q^2+1) + gain.

python3 delorme_ilp.py GQ q SECONDS        GQ in {Q4, W3}
"""
import json
import sys
import time
import importlib.util

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

from lift import ROOT, lib, gq_edges
from gq_clones import q4

spec = importlib.util.spec_from_file_location('d6lift', ROOT / 'research' / 'p4' / 'd6' / 'lift.py')
d6lift = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d6lift)

which, q, secs = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
pts, lines, ovoid = q4(q)
if which == 'W3':  # dual of Q(4,q)
    n0 = len(pts)
    lines = [frozenset(j for j, L in enumerate(lines) if p in L) for p in range(n0)]
n = len(pts)
m = len(lines)
V = n + m
E = gq_edges(n, lines)
nb = [[] for _ in range(V)]
for u, v in E:
    nb[u].append(v)
    nb[v].append(u)
F = len(E)
# variables: x[0:V], a[V:V+F], y[V+F:V+F+V]
nv = 2 * V + F
rows = []
ub = []


def row(coefs, hi):
    rows.append(coefs)
    ub.append(hi)


for v in range(V):  # outside vertex sees <= 1 vertex of C
    row({**{u: 1 for u in nb[v]}, v: -q}, 1)
for f, (p, L) in enumerate(E):
    others_p = [u for u in nb[p] if u != L]
    others_L = [u for u in nb[L] if u != p]
    row({**{u: 1 for u in others_p}, p: q, L: q, V + f: -q}, 2 * q)
    row({**{u: 1 for u in others_L}, p: q, L: q, V + f: q}, 3 * q)
for v in range(V):  # y_v <= x_u for u in N[v]
    for u in nb[v] + [v]:
        row({V + F + v: 1, u: -1}, 0)
A = lil_matrix((len(rows), nv))
for i, r in enumerate(rows):
    for k, c in r.items():
        A[i, k] = c
c = np.zeros(nv)
c[:V] = -1
c[V + F:] = -2
t = time.time()
res = milp(c, constraints=[LinearConstraint(A.tocsr(), -np.inf, np.array(ub))], integrality=np.ones(nv),
           bounds=Bounds(0, 1), options={'time_limit': secs, 'disp': False})
z = np.round(res.x).astype(int)
C = [v for v in range(V) if z[v]]
A1 = [v for v in range(V) if z[V + F + v]]
gain = len(C) + 2 * len(A1)
print(f'{which} q={q}: |A0|={len(C)} |A1|={len(A1)} gain={gain} order={V+gain} status={res.message} '
      f'bound={-getattr(res, "mip_dual_bound", float("nan")):.2f} {time.time()-t:.0f}s', flush=True)
lev = [-1] * V
for v in C:
    lev[v] = 0
for v in A1:
    lev[v] = 1
N, H, _ = d6lift.build(V, nb, lev)
ok = lib.is_valid(N, H, q + 2, 4)
print(f'order {N}, valid(D=4, Delta={q+2}) {ok}')
if ok:
    out = ROOT / 'research' / 'p4' / 'hats' / 'graphs' / f'delorme_{which}_q{q}_n{N}.json'
    out.write_text(json.dumps({'case': f'd{q+2}D4', 'value': N, 'output': [N, [list(e) for e in H]],
                               'A0': C, 'A1': A1}))
    print('wrote', out)
