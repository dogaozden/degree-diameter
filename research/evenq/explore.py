"""Exact whiskers for even q.

mode 'raw':   exact cover of free points by candidate lines (ILP).
mode 'rule':  rule of the odd-q shape: nu : S \\ {v} -> GF(q), F : GF(q)^2 \\ 0 -> GF(q) arbitrary,
              m in S_z is a whisker iff nu(line of S through m cap Pi) = F(z).  (ILP with linearised products.)

python3 explore.py q MODE SECONDS
"""
import json
import sys
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

from frame import Frame

q, mode, secs = int(sys.argv[1]), sys.argv[2], float(sys.argv[3])
t0 = time.time()
Fr = Frame(q)
H, N, lines = Fr.H, Fr.N, Fr.H.lines
zs = [(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)]
cand, cz = [], []
for zi, (a, b) in enumerate(zs):
    for m in Fr.Sz(a, b):
        if m != Fr.v:
            cand.append(int(m))
            cz.append(zi)
cand, cz = np.array(cand), np.array(cz)
fi = -np.ones(N, int)
fi[Fr.free] = np.arange(len(Fr.free))
Xof = np.array([[y for y in lines[m] if Fr.inPi[y]][0] for m in cand])
sof = Fr.Sline_of[Xof]
Sn = [s for s in Fr.S if s != Fr.v]
si = {int(s): i for i, s in enumerate(Sn)}
print(f'[{time.time()-t0:.0f}s] candidates', len(cand), 'free', len(Fr.free), flush=True)


def cover_rows():
    r, c = [], []
    for j, m in enumerate(cand):
        for y in lines[m]:
            if fi[y] >= 0:
                r.append(fi[y]); c.append(j)
    return r, c


if mode == 'raw':
    r, c = cover_rows()
    A = coo_matrix((np.ones(len(r)), (r, c)), shape=(len(Fr.free), len(cand))).tocsr()
    res = milp(np.zeros(len(cand)), constraints=[LinearConstraint(A, 1, 1)], integrality=np.ones(len(cand)),
               bounds=Bounds(0, 1), options={'time_limit': secs})
    print(res.message, flush=True)
    if res.status == 0:
        W = sorted(int(cand[j]) for j in range(len(cand)) if res.x[j] > 0.5)
        print('whiskers', len(W))
        json.dump({'q': q, 'delta': Fr.delta, 'v': Fr.v, 'S': Fr.S.tolist(), 'whiskers': W},
                  open(f'whiskers_raw_q{q}.json', 'w'))
elif mode == 'rule':
    nS, nz = len(Sn), len(zs)
    ny, nf = nS * q, nz * q
    nu_ = len(cand) * q
    nw = len(cand)
    Y = lambda s, c: s * q + c
    Fv = lambda z, c: ny + z * q + c
    U = lambda j, c: ny + nf + j * q + c
    Wv = lambda j: ny + nf + nu_ + j
    nv = ny + nf + nu_ + nw
    rows, cols, vals, lo, hi = [], [], [], [], []
    k = 0

    def add(terms, a, b):
        global k
        for col, val in terms:
            rows.append(k); cols.append(col); vals.append(val)
        lo.append(a); hi.append(b)
        k += 1
    for s in range(nS):
        add([(Y(s, c), 1) for c in range(q)], 1, 1)
    for z in range(nz):
        add([(Fv(z, c), 1) for c in range(q)], 1, 1)
    for j in range(len(cand)):
        s, z = si[int(sof[j])], int(cz[j])
        for c in range(q):
            add([(U(j, c), 1), (Y(s, c), -1)], -np.inf, 0)
            add([(U(j, c), 1), (Fv(z, c), -1)], -np.inf, 0)
            add([(U(j, c), 1), (Y(s, c), -1), (Fv(z, c), -1)], -1, np.inf)
        add([(Wv(j), 1)] + [(U(j, c), -1) for c in range(q)], 0, 0)
    r, c = cover_rows()
    byrow = {}
    for a, b in zip(r, c):
        byrow.setdefault(a, []).append(Wv(b))
    for a, cs in byrow.items():
        add([(x, 1) for x in cs], 1, 1)
    # symmetry breaking: nothing
    A = coo_matrix((vals, (rows, cols)), shape=(k, nv)).tocsr()
    print(f'[{time.time()-t0:.0f}s] ILP vars', nv, 'rows', k, flush=True)
    res = milp(np.zeros(nv), constraints=[LinearConstraint(A, lo, hi)], integrality=np.ones(nv), bounds=Bounds(0, 1),
               options={'time_limit': secs})
    print(f'[{time.time()-t0:.0f}s]', res.message, flush=True)
    if res.status == 0:
        x = res.x
        nu = {int(Sn[s]): next(c for c in range(q) if x[Y(s, c)] > 0.5) for s in range(nS)}
        F = {zs[z]: next(c for c in range(q) if x[Fv(z, c)] > 0.5) for z in range(nz)}
        W = sorted(int(cand[j]) for j in range(len(cand)) if x[Wv(j)] > 0.5)
        print('whiskers', len(W), 'nu value counts', np.unique(list(nu.values()), return_counts=True))
        print('F', F)
        json.dump({'q': q, 'delta': Fr.delta, 'v': Fr.v, 'S': Fr.S.tolist(), 'whiskers': W,
                   'nu': {str(k_): v_ for k_, v_ in nu.items()}, 'F': {f'{a},{b}': v_ for (a, b), v_ in F.items()}},
                  open(f'whiskers_rule_q{q}.json', 'w'))
