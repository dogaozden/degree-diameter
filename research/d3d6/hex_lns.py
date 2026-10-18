"""Large-neighbourhood search (ILP on a ball) for the Theorem C copy problem.
python3 hex_lns.py inst.txt init_sol.txt seconds seed out.txt [depth] [sub_tl]"""
import random, sys, time
from collections import deque
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

inst, init, secs, seed, out = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
depth = int(sys.argv[6]) if len(sys.argv) > 6 else 4
subtl = float(sys.argv[7]) if len(sys.argv) > 7 else 20
rng = random.Random(seed)
f = open(inst); N, K = map(int, f.readline().split())
lines = [list(map(int, f.readline().split())) for _ in range(N)]
thru = [[] for _ in range(N)]
for j, L in enumerate(lines):
    for p in L: thru[p].append(j)
X, W, Y, T = 0, N, 2 * N, 3 * N
A = lil_matrix((6 * N, 4 * N)); ub = []; r = 0
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
A = A.tocsr(); ub = np.array(ub, float)
cons = LinearConstraint(A, -np.inf, ub)
c = np.zeros(4 * N); c[X:X + N] = -1; c[Y:Y + N] = -1
cur = np.zeros(4 * N)
for row in open(init):
    t, x, s = map(int, row.split())
    if t == 0: cur[X + x] = 1; cur[W + x] = (s == 2)
    else: cur[Y + x] = 1; cur[T + x] = (s == 2)
assert (A @ cur <= ub + 1e-9).all()
def save():
    with open(out, 'w') as g:
        for p in range(N):
            if cur[X + p]: g.write(f'0 {p} {2 if cur[W + p] else 1}\n')
        for j in range(N):
            if cur[Y + j]: g.write(f'1 {j} {2 if cur[T + j] else 1}\n')
val = int(-c @ cur); print('start', val, flush=True)
t0 = time.time(); it = 0
while time.time() - t0 < secs:
    it += 1
    # ball in the incidence graph around a random point
    s = rng.randrange(N); dist = {('p', s): 0}; dq = deque([('p', s)])
    d = depth + rng.choice((0, 0, 1)) if depth >= 3 else depth
    while dq:
        v = dq.popleft()
        if dist[v] == d: continue
        nb = [('l', j) for j in thru[v[1]]] if v[0] == 'p' else [('p', p) for p in lines[v[1]]]
        for w in nb:
            if w not in dist: dist[w] = dist[v] + 1; dq.append(w)
            if len(dist) > 2500: break
    free = np.zeros(4 * N, bool)
    for (k, i) in dist:
        if k == 'p': free[X + i] = free[W + i] = True
        else: free[Y + i] = free[T + i] = True
    lb = np.where(free, 0, cur); ubv = np.where(free, 1, cur)
    res = milp(c=c, constraints=cons, integrality=np.ones(4 * N), bounds=Bounds(lb, ubv),
               options={'time_limit': subtl, 'disp': False})
    if res.x is None: continue
    nx = np.round(res.x)
    nv = int(-c @ nx)
    if nv >= val and (A @ nx <= ub + 1e-9).all():
        if nv > val: print(f'it {it} t={time.time()-t0:.0f}s: {val} -> {nv} (free {free.sum()})', flush=True)
        cur, val = nx, nv
        if nv > 0: save()
print('final', val, 'iters', it)
