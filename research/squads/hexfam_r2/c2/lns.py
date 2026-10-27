"""c2: Large Neighbourhood Search for q=9 non-collinear sets in H(9) (at most one point per line).
Each step: pick a region R (ball of incidence-radius 4 around a random point, or the points on k random lines),
drop the current points inside R, keep every other current point fixed, and solve the subproblem exactly with
CP-SAT (num_workers=1). Candidates = points of R not collinear with any kept point. The old points inside R are
feasible in the subproblem (hint). Accept equal-or-larger results (plateau moves), save every improvement.
Usage: python3 -I lns.py TOTAL_SECONDS SEED OUTDIR START_SET [SUB_SECONDS]"""
import sys, time, os, random
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
import numpy as np
from q6lib import Geo
from ortools.sat.python import cp_model

TOTAL = float(sys.argv[1]); SEED = int(sys.argv[2]); OUT = sys.argv[3]; START = sys.argv[4]
SUBT = float(sys.argv[5]) if len(sys.argv) > 5 else 3.0
os.makedirs(OUT, exist_ok=True)
rng = random.Random(SEED); nrng = np.random.default_rng(SEED)
G = Geo(9); N = G.N; L = G.L; LP = G.LP; PL = G.PL
S0 = np.loadtxt(START, dtype=np.int64).reshape(-1)
inS = np.zeros(N, dtype=bool); inS[S0] = True
best = int(inS.sum())
T0 = time.time()
log = open(os.path.join(OUT, 'lns.log'), 'w')
def P(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n'); log.flush()

def save(mask, size):
    fn = os.path.join(OUT, 'best_q9_%d.txt' % size)
    with open(fn, 'w') as f: f.write(' '.join(str(int(v)) for v in np.nonzero(mask)[0]) + '\n')
    return fn

def ball4(c):
    seen = np.zeros(N, dtype=bool); seen[c] = True; cur = np.array([c])
    for _ in range(2):
        lines = np.unique(PL[cur].ravel())
        nxt = np.unique(LP[lines].ravel())
        cur = nxt[~seen[nxt]]; seen[nxt] = True
    return seen

def region_lines(k):
    ls = nrng.choice(L, size=k, replace=False)
    R = np.zeros(N, dtype=bool); R[np.unique(LP[ls].ravel())] = True
    return R

def solve_sub(R):
    """returns (new selection mask restricted to R, status name, n_candidates, n_lines_constrained)"""
    kept = inS & ~R                       # fixed points outside R
    blockedL = kept[LP].any(axis=1)       # lines through a kept point
    blockedP = blockedL[PL].any(axis=1)   # points collinear with a kept point
    C = R & ~blockedP
    cand = np.nonzero(C)[0]
    m = cp_model.CpModel()
    var = {int(p): m.NewBoolVar('p%d' % p) for p in cand}
    ncons = 0
    cl = C[LP]                            # (L,10) candidate flags
    cnt = cl.sum(axis=1)
    for l in np.nonzero(cnt >= 2)[0]:
        pts = LP[l][cl[l]]
        m.AddAtMostOne([var[int(p)] for p in pts]); ncons += 1
    m.Maximize(sum(var.values()))
    old = inS & R & C
    for p in cand:
        m.AddHint(var[int(p)], int(inS[p]))
    s = cp_model.CpSolver()
    s.parameters.num_workers = 1
    s.parameters.max_time_in_seconds = SUBT
    s.parameters.random_seed = rng.randrange(1 << 30)
    s.parameters.symmetry_level = 0
    s.parameters.repair_hint = True
    st = s.StatusName(s.Solve(m))
    newmask = np.zeros(N, dtype=bool)
    if st in ('OPTIMAL', 'FEASIBLE'):
        for p, v in var.items():
            if s.Value(v): newmask[p] = True
    else:
        newmask = old.copy()
    return newmask, st, len(cand), ncons, int(old.sum()), int(newmask.sum()), s.BestObjectiveBound() if st in ('OPTIMAL','FEASIBLE') else -1

it = 0; kmax = int(os.environ.get('KSTART', '1500')); kmin = 200; kcap = 3500; stats = {}
P('start size', best, 'total', TOTAL, 'sub', SUBT)
while time.time() - T0 < TOTAL:
    it += 1
    mode = rng.choice(['ball4', 'lines', 'lines'])
    if mode == 'ball4':
        c = rng.randrange(N); R = ball4(c); arg = c
    else:
        arg = kmax; R = region_lines(kmax)
    ts = time.time()
    newmask, st, nc, ncons, old, new, bd = solve_sub(R)
    dt = time.time() - ts
    # adapt line-region size towards a subproblem of a few hundred candidates
    if mode == 'lines':
        if st == 'OPTIMAL' and dt < 0.5 * SUBT: kmax = min(kcap, int(kmax * 1.15) + 1)
        elif st != 'OPTIMAL': kmax = max(kmin, int(kmax * 0.85))
    if new >= old:
        if new != old or not np.array_equal(newmask, inS & R):
            inS = (inS & ~R) | newmask
    if inS.sum() > best:
        best = int(inS.sum())
        fn = save(inS, best)
        P('IMPROVED', best, fn)
    key = mode
    stats.setdefault(key, [0, 0]); stats[key][0] += 1; stats[key][1] += int(new > old)
    P('it=%d t=%.0f mode=%s arg=%s R=%d cand=%d cons=%d status=%s old=%d new=%d bound=%s dt=%.2f cur=%d kmax=%d' %
      (it, time.time() - T0, mode, arg, int(R.sum()), nc, ncons, st, old, new, bd, dt, int(inS.sum()), kmax))
# final check
Ssel = np.nonzero(inS)[0]
cnt = inS[LP].sum(axis=1)
P('final size', len(Ssel), 'max per line', int(cnt.max()), 'iters', it, 'stats', stats, 'best', best)
save(inS, len(Ssel))
