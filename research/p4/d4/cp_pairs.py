"""Stand-in sets M with every spread line holding 0 or exactly 2 points (pair structure), CP-SAT. usage: q secs [hint.json]"""
import json, sys, time
from ortools.sat.python import cp_model
from w3k import W3
q, secs = int(sys.argv[1]), float(sys.argv[2])
W = W3(q); n = len(W.pts)
m = cp_model.CpModel()
x = [m.NewBoolVar(f'x{i}') for i in range(n)]
for j, L in enumerate(W.lines):
    if W.is_spread_line[j]:
        y = m.NewBoolVar(f'y{j}')
        m.Add(sum(x[p] for p in L) == 2 * y)
    else:
        m.AddAtMostOne([x[p] for p in L])
m.Maximize(sum(x))
class CB(cp_model.CpSolverSolutionCallback):
    def __init__(s): super().__init__(); s.best = 0; s.t0 = time.time()
    def on_solution_callback(s):
        v = int(s.ObjectiveValue())
        if v > s.best:
            s.best = v
            print(f'{time.time()-s.t0:.0f}s |M|={v}', flush=True)
            json.dump({'q': q, 'M': [i for i in range(n) if s.Value(x[i])]}, open(f'sols/pairs_q{q}.json', 'w'))
s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = secs; s.parameters.num_workers = 1
st = s.Solve(m, CB())
print(s.StatusName(st), s.ObjectiveValue(), s.BestObjectiveBound())
