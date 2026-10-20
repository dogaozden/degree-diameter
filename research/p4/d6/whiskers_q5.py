"""Find whiskers for delorme_q5.py: max set of lines through points of S - v (not in S, not meeting v),
pairwise disjoint off S, avoiding points that lie on lines through points of v. Greedy, then MILP (scipy/HiGHS).
Usage: python3 whiskers_q5.py SECONDS"""
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from delorme_q5 import setup  # noqa: E402

P, lines, N, S, through, adj = setup()
Sset = set(S)
v = S[0]
onS = set(p for s in S for p in lines[s])
vlines = set(k for p in lines[v] for k in through[p])
blocked = set(p for k in vlines for p in lines[k]) - onS
cand = [k for k in range(len(lines)) if k not in Sset and k not in vlines]
cand = [k for k in cand if not any(p in blocked for p in lines[k])]
offpts = sorted(set(p for k in cand for p in lines[k]) - onS)
idx = {p: i for i, p in enumerate(offpts)}
print('candidates', len(cand), 'free off-S points', len(offpts), 'bound', len(offpts) // q if (q := 5) else 0)
A = lil_matrix((len(offpts), len(cand)))
for j, k in enumerate(cand):
    for p in lines[k]:
        if p in idx:
            A[idx[p], j] = 1
res = milp(c=-np.ones(len(cand)), constraints=LinearConstraint(A.tocsr(), 0, 1), integrality=np.ones(len(cand)),
           bounds=Bounds(0, 1), options={'time_limit': float(sys.argv[1]), 'disp': False})
x = res.x
W = [cand[j] for j in range(len(cand)) if x is not None and x[j] > 0.5]
print('status', res.status, res.message, 'whiskers', len(W), 'dual bound', -getattr(res, 'mip_dual_bound', float('nan')))
(HERE / 'runs').mkdir(exist_ok=True)
(HERE / 'runs' / f'whiskers_q5_{len(W)}.json').write_text(json.dumps({'whiskers': W}))
