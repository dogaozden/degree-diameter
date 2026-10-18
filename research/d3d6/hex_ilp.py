"""ILP for the Theorem C copy problem in a generalized hexagon (see hex_sa.c for the model).

python3 hex_ilp.py inst.txt time_limit
Variables x_P (point copy), w_P (pure, w <= x), y_L (line copy), t_L (pure, t <= y).
  line L : sum_{P in L} x_P <= 1 + t_L ;  sum_{P in L} w_P <= 1
  point p: sum_{L ni p} y_L <= 1 + w_p ;  sum_{L ni p} t_L <= 1
"""
import sys
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

f = open(sys.argv[1]); N, K = map(int, f.readline().split())
lines = [list(map(int, f.readline().split())) for _ in range(N)]
tl = float(sys.argv[2])
thru = [[] for _ in range(N)]
for j, L in enumerate(lines):
    for p in L:
        thru[p].append(j)
X, W, Y, T = 0, N, 2 * N, 3 * N
A = lil_matrix((6 * N, 4 * N)); ub = []
r = 0
for j, L in enumerate(lines):
    for p in L: A[r, X + p] = 1
    A[r, T + j] = -1; ub.append(1); r += 1
    for p in L: A[r, W + p] = 1
    ub.append(1); r += 1
for p in range(N):
    for j in thru[p]: A[r, Y + j] = 1
    A[r, W + p] = -1; ub.append(1); r += 1
    for j in thru[p]: A[r, T + j] = 1
    ub.append(1); r += 1
for p in range(N):
    A[r, W + p] = 1; A[r, X + p] = -1; ub.append(0); r += 1
    A[r, T + p] = 1; A[r, Y + p] = -1; ub.append(0); r += 1
c = np.zeros(4 * N); c[X:X + N] = -1; c[Y:Y + N] = -1
res = milp(c=c, constraints=LinearConstraint(A.tocsr(), -np.inf, np.array(ub, float)),
           integrality=np.ones(4 * N), bounds=Bounds(0, 1), options={'time_limit': tl, 'disp': True})
print('status', res.status, 'obj', -res.fun if res.x is not None else None, 'bound', -getattr(res, 'mip_dual_bound', 0))
