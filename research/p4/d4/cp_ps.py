"""Theorem B at Delta = q+2 on W(3,q) with a free partial spread P (copied W-lines = point copies of Q(4,q))
and copied W-points M with stand-ins: every t.i. line l has at most 1 + [l in P] points of M. Maximise |P| + |M|.
usage: cp_ps.py q secs"""
import sys, time
from ortools.sat.python import cp_model
from w3k import W3
q, secs = int(sys.argv[1]), float(sys.argv[2])
W = W3(q); n = len(W.pts)
m = cp_model.CpModel()
x = [m.NewBoolVar(f'x{i}') for i in range(n)]
y = [m.NewBoolVar(f'y{j}') for j in range(len(W.lines))]
for p in range(n):
    m.AddAtMostOne([y[j] for j in W.on[p]])
for j, L in enumerate(W.lines):
    m.Add(sum(x[p] for p in L) <= 1 + y[j])
m.Maximize(sum(x) + sum(y))
s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = secs; s.parameters.num_workers = 2
st = s.Solve(m)
P = sum(s.Value(v) for v in y); M = sum(s.Value(v) for v in x)
print(f'q={q} {s.StatusName(st)} |P|+|M|={P+M} (|P|={P}, |M|={M}) bound={s.BestObjectiveBound()} order={2*(q+1)*(q*q+1)+P+M}')
