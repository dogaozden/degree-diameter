#!/usr/bin/env python3
"""Card c6: maximum set of pairwise disjoint lines (partial spread) of H(q): clique constraints per point.
Every partial spread is a dual segment set (no two G-lines meet). usage: spread_mip.py Q TIMELIMIT OUTFILE"""
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
import highspy
from hexload import load
q = int(sys.argv[1]); tl = float(sys.argv[2]); out = sys.argv[3]
qq, N, LP, PL, X = load(f'/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q{q}.bin')
L = N
h = highspy.Highs()
h.setOptionValue('output_flag', True); h.setOptionValue('threads', 1)
h.setOptionValue('time_limit', tl); h.setOptionValue('mip_rel_gap', 0.0)
for j in range(L):
    h.addVar(0.0, 1.0); h.changeColIntegrality(j, highspy.HighsVarType.kInteger); h.changeColCost(j, 1.0)
h.changeObjectiveSense(highspy.ObjSense.kMaximize)
for p in range(N):
    idx = np.array([int(l) for l in PL[p]], dtype=np.int32)
    h.addRow(0.0, 1.0, len(idx), idx, np.ones(len(idx)))
t0 = time.time(); h.run(); dt = time.time() - t0
info = h.getInfo(); sol = h.getSolution().col_value
G = [l for l in range(L) if sol and sol[l] > 0.5]
print(f'SPREAD q={q} primal={info.objective_function_value} dual_bound={info.mip_dual_bound} nG={len(G)} time={dt:.1f}s', flush=True)
open(out, 'w').write('\n'.join(map(str, G)) + '\n')
