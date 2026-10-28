"""Exact maximum relaxed set of W(q) as a set-packing MIP (job d5-relax).
A relaxed set is a union of "units" (single points; collinear pairs) such that every line of W(q) meets at most one unit:
two points of different units on one line would be collinear.  Columns: units (weight 1 or 2), rows: lines (<= 1).
Symmetry: PSp(4,q) is transitive on points and on ordered collinear pairs, so the unit through point 0 is either
case S = the single {0} or case P = the pair {0, p1} for a fixed p1 collinear with 0.  The maximum is the larger of the
two optima.  Option 'S' adds the old spread condition (no pair on a line of the regular spread).
usage: python3 exact_pack.py q [S] [timelimit]"""
import sys, os, itertools, time
import numpy as np
import highspy
HERE = os.path.dirname(os.path.abspath(__file__))
q = int(sys.argv[1]); useS = len(sys.argv) > 2 and sys.argv[2] == 'S'
tl = float(sys.argv[3]) if len(sys.argv) > 3 else 3600
pre = os.path.join(HERE, 'data', 'W%d' % q)
L = [list(map(int, s.split())) for s in open(pre + '_lines.txt').read().strip().split('\n')[1:]]
n = len(L); sp = list(map(int, open(pre + '_spread.txt').read().split()))
plines = [[] for _ in range(n)]
for i, l in enumerate(L):
    for p in l: plines[p].append(i)
units = [((v,), set(plines[v])) for v in range(n)]
for i, l in enumerate(L):
    for a, b in itertools.combinations(l, 2):
        if useS and sp[a] == sp[b]: continue
        units.append(((a, b), set(plines[a]) | set(plines[b])))
p1 = next(b for b in L[plines[0][0]] if b != 0)


def solve(case):
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', tl)
    h.setOptionValue('threads', 1); inf = highspy.kHighsInf
    m = len(units)
    fixed = (0,) if case == 'S' else (0, p1)
    lo = np.array([1.0 if u[0] == fixed else 0.0 for u in units])
    for k in range(m): h.addVar(lo[k], 1.0)
    h.changeColsIntegrality(m, np.arange(m, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * m))
    h.changeColsCost(m, np.arange(m, dtype=np.int32), -np.array([float(len(u[0])) for u in units]))
    rows = [[] for _ in range(n)]
    for k, (pts, ls) in enumerate(units):
        for l in ls: rows[l].append(k)
    for r in rows:
        h.addRow(-inf, 1.0, len(r), np.array(r, dtype=np.int32), np.ones(len(r)))
    t0 = time.time(); h.run()
    sol = h.getSolution().col_value; info = h.getInfo()
    T = sorted(p for k, u in enumerate(units) if sol[k] > 0.5 for p in u[0])
    return h.modelStatusToString(h.getModelStatus()), len(T), -info.mip_dual_bound, time.time() - t0, T


for case in (os.environ['CASE'],) if os.environ.get('CASE') else ('P', 'S'):
    st, size, bd, dt, T = solve(case)
    print('q=%d spread condition %s case %s: %s, best %d, bound %.2f, %.0f s' % (q, useS, case, st, size, bd, dt))
    print('  T', T); sys.stdout.flush()
