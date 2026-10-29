#!/usr/bin/env python3
"""Card c6, goal B: exact ILP (HiGHS via highspy) for the maximum dual segment set of H(q).
Variables: x_l (line in G), y_p (point is a 'hub' allowed to carry several G-lines).
  point p:   sum_{l ~ p} x_l <= 1 + q*y_p           (a point not marked as hub carries at most one G-line)
  pair:      x_l + x_m <= 1 + y_p, l,m through p    (tighter LP form of the same rule)
  line l:    sum_{p in l} y_p <= 1 + (q+1)(1 - x_l) (a G-line contains at most one hub)
  max sum x_l.  Feasible (x,y) <=> G = {x=1} has every G-line meeting the other G-lines in a single point.
usage: ilp.py Q TIMELIMIT OUTFILE [--lb K] [--ub-cut K]"""
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
import highspy
from hexload import load

q = int(sys.argv[1]); tl = float(sys.argv[2]); out = sys.argv[3]
lb = int(sys.argv[sys.argv.index('--lb') + 1]) if '--lb' in sys.argv else None
qq, N, LP, PL, X = load(f'/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q{q}.bin')
L = N
nv = 2 * N                      # columns: x_l = l (0..L-1), y_p = L + p
rows = []                       # (lo, hi, {col: coef})
for p in range(N):
    ls = [int(l) for l in PL[p]]
    rows.append((-highspy.kHighsInf, 1.0, {**{l: 1.0 for l in ls}, L + p: -float(q)}))
    for i in range(len(ls)):
        for j in range(i + 1, len(ls)):
            rows.append((-highspy.kHighsInf, 1.0, {ls[i]: 1.0, ls[j]: 1.0, L + p: -1.0}))
for l in range(L):
    d = {L + int(p): 1.0 for p in LP[l]}
    d[l] = float(q + 1)
    rows.append((-highspy.kHighsInf, float(q + 2), d))
if lb is not None:
    rows.append((float(lb), highspy.kHighsInf, {l: 1.0 for l in range(L)}))

h = highspy.Highs()
h.setOptionValue('output_flag', True)
h.setOptionValue('threads', 1)
h.setOptionValue('time_limit', tl)
h.setOptionValue('mip_rel_gap', 0.0)
h.setOptionValue('mip_abs_gap', 0.999)   # objective is integral
h.setOptionValue('random_seed', 1)
for j in range(nv):
    h.addVar(0.0, 1.0)
    h.changeColIntegrality(j, highspy.HighsVarType.kInteger)
    h.changeColCost(j, 1.0 if j < L else 0.0)
h.changeObjectiveSense(highspy.ObjSense.kMaximize)
for lo, hi, d in rows:
    idx = list(d.keys()); val = [d[k] for k in idx]
    h.addRow(lo, hi, len(idx), np.array(idx, dtype=np.int32), np.array(val, dtype=np.float64))
warm = sys.argv[sys.argv.index('--warm') + 1] if '--warm' in sys.argv else None
if warm:
    G0 = set(int(t) for t in open(warm).read().split())
    cnt = np.zeros(N, int)
    for l in G0:
        cnt[LP[l]] += 1
    vals = [1.0 if l in G0 else 0.0 for l in range(L)] + [1.0 if cnt[p] >= 2 else 0.0 for p in range(N)]
    hs = highspy.HighsSolution(); hs.col_value = vals; hs.value_valid = True
    h.setSolution(hs)
    print(f'warm start |G|={len(G0)}', flush=True)
t0 = time.time()
h.run()
dt = time.time() - t0
info = h.getInfo()
st = h.getModelStatus()
sol = h.getSolution().col_value
G = [l for l in range(L) if sol and sol[l] > 0.5]
print(f'RESULT q={q} model_status={h.modelStatusToString(st)} primal={info.objective_function_value} '
      f'dual_bound={info.mip_dual_bound} nG={len(G)} nodes={info.mip_node_count} time={dt:.1f}s', flush=True)
open(out, 'w').write('\n'.join(map(str, G)) + '\n')
