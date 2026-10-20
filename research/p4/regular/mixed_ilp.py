"""Balanced single-level doubling of H(q): radius-2 trees centred at points AND lines.

A0 = union of trees; each tree = a centre (level 1, all neighbours in A0), the centre's neighbours, and leaves hung on
those neighbours. Every vertex outside A0 sees at most one A0 vertex (Theorem 1 (b)); trees have diameter <= 4
(Lemma 2), so Theorem 1 gives diameter 6 with m = 2. Balance: the extra vertices a + 2c are equal on both sides.

Variables a_x (in A0), c_x (centre). Cn_y = sum of c over N(y); leaf_y = a_y - c_y - Cn_y.
python3 mixed_ilp.py q SECONDS [exact]
"""
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

ROOT = Path(__file__).resolve().parents[3]
q, secs = int(sys.argv[1]), float(sys.argv[2])
exact = 'exact' in sys.argv
lines = json.loads((ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json').read_text())['lines']
N = len(lines)
V = 2 * N
adj = [[] for _ in range(V)]
for k, L in enumerate(lines):
    for p in L:
        adj[p].append(N + k)
        adj[N + k].append(p)
edges = [(p, N + k) for k, L in enumerate(lines) for p in L]
A, C = 0, V  # variable offsets
nv = 2 * V
rows = []
lo, hi = [], []


def add(coef, l, h):
    rows.append(coef)
    lo.append(l)
    hi.append(h)


for y in range(V):
    # c_y <= a_y
    add({C + y: 1, A + y: -1}, -np.inf, 0)
    # c_y + Cn_y <= 1 ; a_y - c_y - Cn_y >= 0
    d = {C + y: 1}
    for z in adj[y]:
        d[C + z] = d.get(C + z, 0) + 1
    add(d, -np.inf, 1)
    d2 = {A + y: 1, C + y: -1}
    for z in adj[y]:
        d2[C + z] = d2.get(C + z, 0) - 1
    add(d2, 0, np.inf)
    # outside sees <= 1 (exact: >= 1 too): sum a_z - q a_y <= 1
    d3 = {A + y: -q}
    for z in adj[y]:
        d3[A + z] = 1
    add(d3, -np.inf, 1)
    if exact:
        add({A + z: 1 for z in adj[y]}, 1, np.inf)
    # leaf has exactly one A0 neighbour: sum a_z + q*(a_y - c_y - Cn_y) <= 1 + q
    d4 = {A + z: 1 for z in adj[y]}
    d4[A + y] = d4.get(A + y, 0) + q
    d4[C + y] = d4.get(C + y, 0) - q
    for z in adj[y]:
        d4[C + z] = d4.get(C + z, 0) - q
    add(d4, -np.inf, 1 + q)
for (y, z) in edges:
    for (s, t) in ((y, z), (z, y)):
        # centre s -> t in A0
        add({C + s: 1, A + t: -1}, -np.inf, 0)
        # leaf s -> its A0 neighbour t is a centre-neighbour: a_t - Cn_t + a_s - c_s - Cn_s <= 1
        d = {A + t: 1, A + s: 1, C + s: -1}
        for w in adj[t]:
            d[C + w] = d.get(C + w, 0) - 1
        for w in adj[s]:
            d[C + w] = d.get(C + w, 0) - 1
        add(d, -np.inf, 1)
    # adjacent centre-neighbours forbidden: Cn_y + Cn_z <= 1
    d = {}
    for w in adj[y] + adj[z]:
        d[C + w] = d.get(C + w, 0) + 1
    add(d, -np.inf, 1)
# balance: sum_P (a + 2c) = sum_L (a + 2c)
d = {}
for x in range(V):
    s = 1 if x < N else -1
    d[A + x] = s
    d[C + x] = 2 * s
add(d, 0, 0)
M = lil_matrix((len(rows), nv))
for i, r in enumerate(rows):
    for j, val in r.items():
        if val:
            M[i, j] = val
obj = np.zeros(nv)
obj[A:A + V] = -1
obj[C:C + V] = -2
t0 = time.time()
print('q', q, 'N', N, 'rows', len(rows), 'exact', exact, flush=True)
res = milp(obj, constraints=[LinearConstraint(M.tocsr(), lo, hi)], integrality=np.ones(nv), bounds=Bounds(0, 1),
           options={'time_limit': secs, 'disp': False})
print(res.message, 'time', round(time.time() - t0), flush=True)
if res.x is not None:
    x = np.round(res.x).astype(int)
    a, c = x[A:A + V], x[C:C + V]
    gain = int(a.sum() + 2 * c.sum())
    print('gain', gain, 'bound', -res.mip_dual_bound if hasattr(res, 'mip_dual_bound') else None,
          'A0 points/lines', int(a[:N].sum()), int(a[N:].sum()), 'centres points/lines', int(c[:N].sum()),
          int(c[N:].sum()), 'order', 2 * N + gain)
    out = Path(__file__).resolve().parent / f'mixed_q{q}{"_exact" if exact else ""}.json'
    out.write_text(json.dumps({'q': q, 'A0': np.nonzero(a)[0].tolist(), 'A1': np.nonzero(c)[0].tolist()}))
    print('wrote', out)
