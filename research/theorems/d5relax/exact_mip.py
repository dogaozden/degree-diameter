"""Exact maximum relaxed set of W(q) by MIP (HiGHS), with or without the old spread condition (job d5-relax).
Relaxed: every point of T is collinear with at most one other point of T.  Constraints: at most 2 points of T on a line;
for every point v and two lines L1 != L2 through v: x(L1 - v) + x(L2 - v) + 3 x_v <= 4.  With 'S' also: at most one point
on each line of the regular spread.  x_0 = 1 (PSp(4,q) is transitive on points).
usage: python3 exact_mip.py q [S] [timelimit]"""
import sys, os, itertools, time
import numpy as np
import highspy
HERE = os.path.dirname(os.path.abspath(__file__))
q = int(sys.argv[1]); useS = len(sys.argv) > 2 and sys.argv[2] == 'S'
tl = float(sys.argv[3]) if len(sys.argv) > 3 else 3600
pre = os.path.join(HERE, 'data', 'W%d' % q)
L = [list(map(int, s.split())) for s in open(pre + '_lines.txt').read().strip().split('\n')[1:]]
n = (q + 1) * (q * q + 1); assert len(L) == n
sp = list(map(int, open(pre + '_spread.txt').read().split()))
plines = [[] for _ in range(n)]
for i, l in enumerate(L):
    for p in l: plines[p].append(i)
h = highspy.Highs(); h.setOptionValue('output_flag', True); h.setOptionValue('time_limit', tl)
h.setOptionValue('threads', 1)
inf = highspy.kHighsInf
for v in range(n):
    h.addVar(1.0 if v == 0 else 0.0, 1.0)
h.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * n))
h.changeColsCost(n, np.arange(n, dtype=np.int32), -np.ones(n))
def row(idx, ub):
    idx = sorted(set(idx)); h.addRow(-inf, ub, len(idx), np.array(idx, dtype=np.int32), np.ones(len(idx)))
for l in L: row(l, 2)
for v in range(n):
    for a, b in itertools.combinations(plines[v], 2):
        idx = sorted(set(L[a] + L[b]) - {v}) + [v]
        h.addRow(-inf, 4, len(idx), np.array(idx, dtype=np.int32), np.array([1.0] * (len(idx) - 1) + [3.0]))
if useS:
    for s in range(q * q + 1):
        row([p for p in range(n) if sp[p] == s], 1)
t0 = time.time(); h.run()
info = h.getInfo(); sol = h.getSolution().col_value
T = [v for v in range(n) if sol[v] > 0.5]
print('q=%d spread condition %s: status %s, best %d, bound %.2f, %.0f s' % (
    q, useS, h.modelStatusToString(h.getModelStatus()), len(T), -info.mip_dual_bound, time.time() - t0))
print('T', T)
