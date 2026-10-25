#!/usr/bin/env python3
"""Backtrack-complete vertices in the frame gauge (EDGECHART.md).  Apexes = e_0..e_3.  Apex i has a leg triangle T_i
(3 non-collinear points of the quotient PG(F^4/e_i), none of them a frame point e_j).  The vertex is complete iff the
6 frame lines and the 12 legs <e_i, q>, q in T_i, cover PG(3,3).  Enumerates complete (T_0..T_3)."""
import itertools, sys, pickle
def norm(v):
    v = tuple(x % 3 for x in v)
    for x in v:
        if x: return tuple((y * x) % 3 for y in v)   # x^-1 = x in F_3
    return None
PTS = sorted({norm(v) for v in itertools.product(range(3), repeat=4) if any(v)})
IDX = {p: i for i, p in enumerate(PTS)}
E = [tuple(int(r == i) for r in range(4)) for i in range(4)]
def add(u, v, a=1, b=1): return norm(tuple(a * x + b * y for x, y in zip(u, v)))
def line_pts(u, v): return {add(u, v, a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)}
frame_cov = set()
for i, j in itertools.combinations(range(4), 2): frame_cov |= line_pts(E[i], E[j])
REST = [p for p in PTS if p not in frame_cov]; RI = {p: t for t, p in enumerate(REST)}
assert len(REST) == 24
def rank(vs):
    rows = [list(v) for v in vs]; r = 0
    for c in range(4):
        piv = next((k for k in range(r, len(rows)) if rows[k][c] % 3), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]; inv = rows[r][c] % 3
        rows[r] = [(x * inv) % 3 for x in rows[r]]
        for k in range(len(rows)):
            if k != r and rows[k][c] % 3:
                f = rows[k][c]; rows[k] = [(x - f * y) % 3 for x, y in zip(rows[k], rows[r])]
        r += 1
    return r
QP = []   # quotient points for apex i: normalized vectors with coordinate i = 0, not a frame point
TRI = []  # per apex: list of (triangle tuple, coverage mask over REST)
for i in range(4):
    qs = [p for p in PTS if p[i] == 0 and p not in E]
    QP.append(qs); tris = []
    for T in itertools.combinations(qs, 3):
        if rank(list(T) + [E[i]]) < 4: continue          # legs must be independent mod e_i
        m = 0
        for q in T:
            for p in line_pts(E[i], q):
                if p in RI: m |= 1 << RI[p]
        tris.append((T, m))
    TRI.append(tris)
print('quotient points per apex', [len(q) for q in QP], 'triangles per apex', [len(t) for t in TRI])
FULL = (1 << 24) - 1
# meet in the middle
from collections import defaultdict
m01 = defaultdict(list); m23 = defaultdict(list)
for a, (Ta, ma) in enumerate(TRI[0]):
    for b, (Tb, mb) in enumerate(TRI[1]): m01[ma | mb].append((a, b))
for c, (Tc, mc) in enumerate(TRI[2]):
    for d, (Td, md) in enumerate(TRI[3]): m23[mc | md].append((c, d))
print('distinct masks', len(m01), len(m23))
sols = []
k23 = list(m23.items())
for mA, lA in m01.items():
    need = FULL & ~mA
    for mB, lB in k23:
        if mB & need == need:
            for x in lA:
                for y in lB: sols.append(x + y)
print('complete assignments', len(sols))
pickle.dump({'PTS': PTS, 'TRI': [[T for T, m in t] for t in TRI], 'sols': sols}, open('complete.pkl', 'wb'))
