"""c2: CP-SAT model for q=9 non-collinear sets in H(9).
One boolean per point; AddAtMostOne over the 10 points of every line; maximise the sum.
Hint = the 4306 set. Usage: python3 -I cpsat.py TIME_SECONDS SEED OUTDIR [HINTFILE]
Solutions are written to OUTDIR/best_q9_<size>.txt whenever they improve on the best so far."""
import sys, time, os
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
import numpy as np
from q6lib import Geo
from ortools.sat.python import cp_model

TL = float(sys.argv[1]); SEED = int(sys.argv[2]); OUT = sys.argv[3]
HINT = sys.argv[4] if len(sys.argv) > 4 else '/home/user/degree-diameter/research/projects/hexagon-family/sets/P9_ncol_4306.txt'
os.makedirs(OUT, exist_ok=True)
G = Geo(9)
N = G.N
hint = np.loadtxt(HINT, dtype=np.int64).reshape(-1)
hs = np.zeros(N, dtype=bool); hs[hint] = True
T0 = time.time()

m = cp_model.CpModel()
x = [m.NewBoolVar('x%d' % i) for i in range(N)]
for l in range(G.L):
    m.AddAtMostOne([x[p] for p in G.LP[l]])
m.Maximize(sum(x))
for i in range(N):
    m.AddHint(x[i], int(hs[i]))
print('model built', time.time() - T0, 's', flush=True)

best = [len(hint)]
def save(sel, size):
    fn = os.path.join(OUT, 'best_q9_%d.txt' % size)
    with open(fn, 'w') as f:
        f.write(' '.join(str(int(v)) for v in sel) + '\n')
    return fn

class CB(cp_model.CpSolverSolutionCallback):
    def __init__(self):
        super().__init__()
    def on_solution_callback(self):
        obj = int(self.ObjectiveValue()); bd = self.BestObjectiveBound()
        print('t=%.1f sol obj=%d bound=%.1f' % (time.time() - T0, obj, bd), flush=True)
        if obj > best[0]:
            sel = np.array([i for i in range(N) if self.Value(x[i])])
            # verify the constraint before saving
            cnt = np.zeros(G.L, dtype=np.int64); s = np.zeros(N, dtype=bool); s[sel] = True
            assert (s[G.LP].sum(1) <= 1).all()
            best[0] = len(sel)
            print('saved', save(sel, len(sel)), flush=True)

solver = cp_model.CpSolver()
solver.parameters.num_workers = 1
solver.parameters.max_time_in_seconds = TL
solver.parameters.random_seed = SEED
solver.parameters.log_search_progress = True
solver.parameters.symmetry_level = int(os.environ.get('SYMLEV', '0'))
solver.parameters.repair_hint = True
st = solver.Solve(m, CB())
print('status', solver.StatusName(st), 'obj', solver.ObjectiveValue(), 'bound', solver.BestObjectiveBound(), flush=True)
print('wall', time.time() - T0, flush=True)
