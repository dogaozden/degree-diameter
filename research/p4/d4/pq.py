"""Problem P(q): the antipodal-pair form of the stand-in problem at Delta = q+2 (q odd).

K = GF(q^2), F = GF(q), t = (q+1)/2, H = F* u omega F* = <gamma^t> (omega traceless). Spread lines of W(3,q) are the
points z of PG(1,q^2), with vector v_z = (1,z) or v_inf = (0,1). On line z we pick an "antipodal pair"
{<w>_F, <omega w>_F} with w = gamma^r v_z; only r mod t matters. Two pairs on lines z, z' are compatible exactly when
det(w, w') is not in H, i.e. r + r' + log det(v_z, v_z') != 0 (mod t).
A compatible family A of pairs gives |M| = 2|A| line copies of Q(4,q) (dually), so order
2(q+1)(q^2+1) + (q^2+1) + 2|A|.

usage: python pq.py q seconds [--workers 2] [--sym k]   (--sym k: require invariance under z -> gamma^(k) ... see code)
"""
import argparse
import json
import sys
import time
from pathlib import Path

from ortools.sat.python import cp_model

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('q', type=int)
ap.add_argument('secs', type=float)
ap.add_argument('--workers', type=int, default=2)
ap.add_argument('--lb', type=int, default=0)
ap.add_argument('--hint', default=None)
ap.add_argument('--out', default=None)
args = ap.parse_args()
q = args.q
Q = q * q
K = lib.GF(Q)
t = (q + 1) // 2
log = K._log
sub = K.sub
INF = Q  # index of the point at infinity


def ldet(z, z2):
    """log det(v_z, v_z2) mod t."""
    if z == INF or z2 == INF:
        return 0
    return int(log[sub(z2, z)]) % t


m = cp_model.CpModel()
x = [[m.NewBoolVar(f'x{z}_{r}') for r in range(t)] for z in range(Q + 1)]
for z in range(Q + 1):
    m.AddAtMostOne(x[z])
for z in range(Q + 1):
    for z2 in range(z + 1, Q + 1):
        c = ldet(z, z2)
        for r in range(t):
            r2 = (-r - c) % t
            m.AddBoolOr([x[z][r].Not(), x[z2][r2].Not()])
# symmetry breaking: lines infinity and 0 are used (SL(2,q^2) is 2-transitive) and r_inf = 0 (diag(a, 1/a))
m.Add(x[INF][0] == 1)
m.Add(sum(x[0]) == 1)
obj = sum(x[z][r] for z in range(Q + 1) for r in range(t))
if args.lb:
    m.Add(obj >= args.lb)
m.Maximize(obj)
s = cp_model.CpSolver()
s.parameters.max_time_in_seconds = args.secs
s.parameters.num_workers = args.workers
t0 = time.time()


class CB(cp_model.CpSolverSolutionCallback):
    def __init__(self):
        super().__init__()
        self.best = 0

    def on_solution_callback(self):
        v = int(self.ObjectiveValue())
        if v > self.best:
            self.best = v
            A = [(z, r) for z in range(Q + 1) for r in range(t) if self.Value(x[z][r])]
            print(f'  {time.time() - t0:.0f}s |A|={v} |M|={2 * v} bound={self.BestObjectiveBound()}', flush=True)
            if args.out:
                Path(args.out).write_text(json.dumps({'q': q, 'A': A}))


st = s.Solve(m, CB())
print(f'q={q} t={t} status={s.StatusName(st)} |A|={int(s.ObjectiveValue()) if st in (2, 4) else 0} '
      f'bound={s.BestObjectiveBound()} |M|={2 * int(s.ObjectiveValue()) if st in (2, 4) else 0} '
      f'time={time.time() - t0:.1f}s', flush=True)
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    A = [(z, r) for z in range(Q + 1) for r in range(t) if s.Value(x[z][r])]
    for i, (z, r) in enumerate(A):
        for z2, r2 in A[i + 1:]:
            assert (r + r2 + ldet(z, z2)) % t != 0
    if args.out:
        Path(args.out).write_text(json.dumps({'q': q, 'A': A}))
