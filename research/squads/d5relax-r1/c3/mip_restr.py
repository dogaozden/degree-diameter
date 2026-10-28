"""Spread-restricted relaxed sets of W(q) by MIP (HiGHS).  Restricted model: T is a set of points with
at most 1 point on each non-spread line of W(q) and at most 2 points on each line of the regular spread.
(Equivalent to: every pair of T lies on a spread line, and T is relaxed.)
usage: python3 mip_restr.py q timelimit outfile [startfile]"""
import sys, os, time
import numpy as np
import highspy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wstruct import load
q = int(sys.argv[1]); tl = float(sys.argv[2]); outf = sys.argv[3]
start = sys.argv[4] if len(sys.argv) > 4 else None
adj, L, sp = load(q); n = len(adj); S = q * q + 1
spl = [[p for p in range(n) if sp[p] == s] for s in range(S)]
spset = set(frozenset(x) for x in spl)
nonsp = [l for l in L if frozenset(l) not in spset]
h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', tl)
h.setOptionValue('threads', 1); h.setOptionValue('mip_rel_gap', 0.0)
inf = highspy.kHighsInf
h.addVars(n, np.zeros(n), np.ones(n))
h.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * n))
h.changeColsCost(n, np.arange(n, dtype=np.int32), -np.ones(n))
for l in nonsp:
    h.addRow(-inf, 1, len(l), np.array(l, dtype=np.int32), np.ones(len(l)))
for s in spl:
    h.addRow(-inf, 2, len(s), np.array(s, dtype=np.int32), np.ones(len(s)))
if start:
    st = open(start).read().split(); m = int(st[0]); vs = [int(x) for x in st[1:1 + m]]
    sol = highspy.HighsSolution(); x0 = np.zeros(n)
    x0[vs] = 1.0; sol.col_value = list(x0); sol.value_valid = True
    print('warm start', h.setSolution(sol))
t0 = time.time(); h.run()
info = h.getInfo(); sol = h.getSolution().col_value
T = [v for v in range(n) if sol[v] > 0.5]
# verify restricted
C = np.zeros((n, n), dtype=int)
for v in range(n):
    for u in adj[v]: C[v, u] = 1
A = np.array(T)
ok_relaxed = bool(C[np.ix_(A, A)].sum(1).max() <= 1)
ok_restr = all(sum(1 for v in T if sp[v] == s) <= 2 for s in range(S)) and \
    all(sum(1 for v in l if v in set(T)) <= 1 for l in nonsp)
with open(outf, 'w') as f:
    f.write('%d\n' % len(T)); f.write(''.join('%d\n' % v for v in T))
print(json_line := 'q=%d status=%s size=%d bound=%.2f time=%.1f relaxed=%s restricted=%s' % (
    q, h.modelStatusToString(h.getModelStatus()), len(T), -info.mip_dual_bound, time.time() - t0, ok_relaxed, ok_restr))
