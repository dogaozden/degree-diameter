"""Largest partial spread (pairwise disjoint lines) of Q(4,q) by ILP, to close the k_o <= 1 case of opart2.py."""
import sys
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
from lift import lib  # noqa: F401  (sets sys.path)
from gq_clones import q4
q, secs = int(sys.argv[1]), float(sys.argv[2])
pts, lines, ovoid = q4(q)
A = lil_matrix((len(pts), len(lines)))
for j, L in enumerate(lines):
    for p in L:
        A[p, j] = 1
r = milp(-np.ones(len(lines)), constraints=[LinearConstraint(A.tocsr(), 0, 1)], integrality=np.ones(len(lines)),
         bounds=Bounds(0, 1), options={'time_limit': secs})
print(f'q={q}: partial spread {int(round(-r.fun))}, bound {-r.mip_dual_bound:.2f}, {r.message}')
