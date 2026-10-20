"""Exact max of the stand-in problem (mode st) with one point fixed in M (the spread stabiliser is point-transitive).
usage: cp_st_exact.py q secs workers"""
import sys
from ortools.sat.python import cp_model
from w3k import W3
q, secs, wk = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
W = W3(q); n = len(W.pts)
m = cp_model.CpModel()
x = [m.NewBoolVar(f'x{i}') for i in range(n)]
for j, L in enumerate(W.lines):
    m.Add(sum(x[p] for p in L) <= (2 if W.is_spread_line[j] else 1))
m.Add(x[0] == 1)
m.Add(sum(x) <= q * q - q + 2)  # proved upper bound
m.Maximize(sum(x))
s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = secs; s.parameters.num_workers = wk
st = s.Solve(m)
print(f'q={q} {s.StatusName(st)} best={s.ObjectiveValue()} bound={s.BestObjectiveBound()}', flush=True)
