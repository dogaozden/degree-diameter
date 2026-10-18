"""Given point copies W = Q_1 + Q_2 + O (O a partial ovoid file), find the most line copies M with every point p on at
most 1 + w(p) entries (stand-ins, Theorem B), degree q+3. python3 fixedw_m_ilp.py q OVOID.txt SECONDS -> runs/fixedw_q{q}.json"""
import json, sys
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from as_gq import build
from as_w2 import weighted_2ovoid
q, secs = int(sys.argv[1]), float(sys.argv[3])
F, pts, lines = build(q)
W, _, _ = weighted_2ovoid(F, pts)
W.update(Counter(int(x) for x in Path(sys.argv[2]).read_text().split()))
n, m = len(pts), len(lines)
A = lil_matrix((n, m))
for j, L in enumerate(lines):
    for p in L:
        A[p, j] = 1
cap = np.array([1 + W[p] for p in range(n)])
res = milp(-np.ones(m), constraints=[LinearConstraint(A.tocsr(), 0, cap)], integrality=np.ones(m),
           bounds=Bounds(0, 1), options={'time_limit': secs, 'disp': False})
x = np.round(res.x).astype(int)
M = [j for j in range(m) if x[j]]
print(f'q={q}: |W|={sum(W.values())} |M|={len(M)} order={n+m+sum(W.values())+len(M)} {res.message} bound={getattr(res,"mip_dual_bound",None)}')
(HERE / 'runs' / f'fixedw_q{q}.json').write_text(json.dumps({'w': {str(p): c for p, c in W.items()}, 'M': M}))
