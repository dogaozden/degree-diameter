"""Mixed centres in H(q): random greedy set of k line centres and k point centres, pairwise at distance >= 5, then the
leaf ILP (each vertex outside A0 sees <= 1 A0 vertex; exact: == 1). Small q only (all-pairs distances).

python3 mixcode.py q k SECONDS TRIES [exact]
"""
import json
import random
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix, lil_matrix
from scipy.sparse.csgraph import shortest_path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
q, k, secs, tries = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
exact = 'exact' in sys.argv
lines = json.loads((ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json').read_text())['lines']
N = len(lines)
V = 2 * N
r_ = [p for kk, L in enumerate(lines) for p in L]
c_ = [N + kk for kk, L in enumerate(lines) for p in L]
G = csr_matrix((np.ones(2 * len(r_)), (r_ + c_, c_ + r_)), shape=(V, V))
D = shortest_path(G, unweighted=True).astype(int)
adj = [[] for _ in range(V)]
for a, b in zip(r_, c_):
    adj[a].append(b)
    adj[b].append(a)
best = None
for t in range(tries):
    rng = random.Random(t)
    order = list(range(V))
    rng.shuffle(order)
    C, nP, nL = [], 0, 0
    for x in order:
        if (x < N and nP >= k) or (x >= N and nL >= k):
            continue
        if all(D[x, y] >= 5 for y in C):
            C.append(x)
            nP += x < N
            nL += x >= N
    if nP < k or nL < k:
        continue
    fixed = set(C) | {y for x in C for y in adj[x]}
    cand = sorted({z for x in C for y in adj[x] for z in adj[y]} - fixed)
    ci = {z: i for i, z in enumerate(cand)}
    M = lil_matrix((V, len(cand)))
    lo, hi = [], []
    row = 0
    for y in range(V):
        if y in fixed:
            continue
        F = sum(z in fixed for z in adj[y])
        for z in adj[y]:
            if z in ci:
                M[row, ci[z]] = 1
        lo.append(1 - F if exact else -np.inf)
        hi.append(1 - F)
        row += 1
    res = milp(-np.ones(len(cand)), constraints=[LinearConstraint(M[:row].tocsr(), lo, hi)],
               integrality=np.ones(len(cand)), bounds=Bounds(0, 1), options={'time_limit': secs})
    if res.x is None:
        print('try', t, res.message[:40], flush=True)
        continue
    x = np.round(res.x).astype(int)
    A0 = fixed | {cand[i] for i in range(len(cand)) if x[i]}
    aP = sum(1 for z in A0 if z < N)
    aL = len(A0) - aP
    sides = (N + aP + 2 * k, N + aL + 2 * k)
    print('try', t, 'A0 points', aP, 'lines', aL, 'exact value', (N - 2 * k) // q, 'sides', sides,
          'balanced order', 2 * min(sides), flush=True)
    if best is None or min(sides) > min(best[0]):
        best = (sides, C, sorted(A0))
if best:
    (HERE / f'mixcode_q{q}_k{k}.json').write_text(json.dumps({'q': q, 'sides': best[0], 'centres': best[1],
                                                              'A0': best[2]}))
    print('best sides', best[0])
