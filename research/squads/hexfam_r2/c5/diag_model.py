"""CP-SAT for the max clique A in the chart: A subset GF(q)^5, Q'(u-v) != 0 for u != v in A; answer = 1 + |A|.
Model: 0 and w1 fixed in A (translation; scaling so that Q'(w1)=1 or the nonsquare n; O(Q') transitive on each value).
Conflicts Q'(u-v)=0 are covered by AtMostOne constraints on the cosets of every totally singular plane W
(each singular difference lies in a maximal totally singular plane, and a coset of W is a conflict clique).
Usage: cpsat_chart.py q hintchart.txt seconds outset.txt
"""
import sys, os, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c5')
from chartlib import *
from ortools.sat.python import cp_model

q = int(sys.argv[1]); hintfile = sys.argv[2]; tlim = float(sys.argv[3]); outpath = sys.argv[4]
G = Geo(q)
e4 = e4_id(G)
hint_pts = eval(open(hintfile).read())            # chart tuples, may contain (0,0,0,0,0)
Qp = lambda t: (t[2] * t[2] - t[0] * t[3] - t[1] * t[4]) % q
sq = {x * x % q for x in range(1, q)}
nonres = min(x for x in range(1, q) if x not in sq)

# ---- normalise: translate so 0 is in A, scale so that some v in A has Q'(v) = 1 (square case) or n (nonsquare)
a0 = hint_pts[0]
T = [tuple((x - y) % q for x, y in zip(t, a0)) for t in hint_pts]
cand = [t for t in T if t != (0, 0, 0, 0, 0) and Qp(t) != 0 and Qp(t) in sq]
target = 1
if not cand:
    cand = [t for t in T if t != (0, 0, 0, 0, 0) and Qp(t) != 0]
    target = nonres
v = cand[0]
lam = next(l for l in range(1, q) if (l * l * Qp(v)) % q == target)
S = [tuple((lam * x) % q for x in t) for t in T]
w1 = tuple((lam * x) % q for x in v)
assert Qp(w1) == target and (0,) * 5 in S and w1 in S
print('case target Q\'=', target, 'hint size', len(S), flush=True)

# ---- vectors
idx = np.arange(q ** 5, dtype=np.int64)
V = np.stack([(idx // q ** i) % q for i in range(5)], axis=1)        # columns a,b,c,e,f ; code = sum V_i q^i
code = lambda t: int(sum(int(t[i]) * q ** i for i in range(5)))
Bm = np.zeros((5, 5), dtype=np.int64)                                 # B'(x,y) = x^T Bm y, Bm[c,c]=2, a-e, b-f
Bm[2, 2] = 2
Bm[0, 3] = Bm[3, 0] = -1
Bm[1, 4] = Bm[4, 1] = -1
Qv = (V[:, 2] ** 2 - V[:, 0] * V[:, 3] - V[:, 1] * V[:, 4]) % q
Dv = (V - np.array(w1)) % q
Qd = (Dv[:, 2] ** 2 - Dv[:, 0] * Dv[:, 3] - Dv[:, 1] * Dv[:, 4]) % q
D = np.nonzero((Qv != 0) & (Qd != 0))[0]
Vd = V[D]
print('domain', len(D), flush=True)

# ---- totally singular planes: lines of the parabolic quadric in PG(4,q)
sing = np.nonzero(Qv == 0)[0]
sing = sing[sing != 0]
Vs = V[sing]
first = np.argmax(Vs != 0, axis=1)
P = Vs[Vs[np.arange(len(Vs)), first] == 1]                        # projective singular points
def normalize(v):
    v = [int(x) % q for x in v]
    f = next(i for i, x in enumerate(v) if x)
    iv = inv(v[f], q)
    return tuple((x * iv) % q for x in v)
pidx = {tuple(int(x) for x in row): k for k, row in enumerate(P)}
GM = (P @ Bm @ P.T) % q
planes, seen = [], set()
for i in range(len(P)):
    for j in np.nonzero(GM[i, i + 1:] == 0)[0] + i + 1:
        pts = {pidx[normalize(P[i] * al + P[j] * be)] for al, be in [(1, t) for t in range(q)] + [(0, 1)]}
        key = tuple(sorted(pts))
        if key not in seen:
            seen.add(key)
            planes.append((P[i], P[j]))
assert len(planes) == (q + 1) * (q * q + 1), len(planes)
print('totally singular planes', len(planes), flush=True)

# ---- model
m = cp_model.CpModel()
xs = [m.NewBoolVar('x%d' % k) for k in range(len(D))]
pos = {int(u): k for k, u in enumerate(D)}
ngroups = 0
for d1, d2 in planes:
    Ns = nullspace_mod(np.stack([(d1 @ Bm) % q, (d2 @ Bm) % q]), q)
    assert len(Ns) == 3
    vals = (Vd @ Bm @ np.array(Ns).T) % q
    cc = vals @ (q ** np.arange(3))
    order = np.argsort(cc, kind='stable')
    splits = np.flatnonzero(np.diff(cc[order])) + 1
    for g in np.split(order, splits):
        if len(g) >= 2:
            m.AddAtMostOne([xs[k] for k in g])
            ngroups += 1
print('AtMostOne groups', ngroups, flush=True)

hs_chk = {code(t) for t in S if t != (0,) * 5 and t != w1}
viol = 0; ngrp = 0
for d1, d2 in planes:
    Ns = nullspace_mod(np.stack([(d1 @ Bm) % q, (d2 @ Bm) % q]), q)
    vals = (Vd @ Bm @ np.array(Ns).T) % q
    cc = vals @ (q ** np.arange(3))
    order = np.argsort(cc, kind='stable')
    splits = np.flatnonzero(np.diff(cc[order])) + 1
    for g in np.split(order, splits):
        if len(g) >= 2:
            ngrp += 1
            hit = sum(1 for k in g if int(D[k]) in hs_chk)
            if hit > 1: viol += 1
print('CHECK groups', ngrp, 'violated by hint', viol, flush=True)
m.Maximize(cp_model.LinearExpr.Sum(xs))

# hint (must be feasible: a clique)
hs = {code(t) for t in S if t != (0,) * 5 and t != w1}
for k, u in enumerate(D):
    m.AddHint(xs[k], 1 if int(u) in hs else 0)
print('hint inside domain', len(hs), 'in D', sum(1 for u in hs if int(u) in pos), flush=True)
fixed_pts = [(0,) * 5, w1]
ntotal_fixed = 1 + len(fixed_pts)     # e4 + 0 + w1

class CB(cp_model.CpSolverSolutionCallback):
    def __init__(self):
        super().__init__()
        self.best = 0
        self.t0 = time.time()
    def on_solution_callback(self):
        chosen = [int(D[k]) for k in range(len(D)) if self.Value(xs[k])]
        tot = ntotal_fixed + len(chosen)
        if tot > self.best:
            self.best = tot
            pts = fixed_pts + [tuple(int(x) for x in V[c]) for c in chosen]
            save_set(outpath, [e4] + ids_of_chart(G, pts))
            print('SOL total %d  bound %d  t=%.1f' % (tot, ntotal_fixed + self.BestObjectiveBound(), time.time() - self.t0), flush=True)

solver = cp_model.CpSolver()
solver.parameters.num_workers = 1
if os.environ.get('NOPRE'): solver.parameters.cp_model_presolve = False
solver.parameters.max_time_in_seconds = tlim
solver.parameters.log_search_progress = True
cb = CB()
st = solver.Solve(m, cb)
print('STATUS', solver.StatusName(st), 'obj total', ntotal_fixed + solver.ObjectiveValue(),
      'bound total', ntotal_fixed + solver.BestObjectiveBound(), 'wall', round(solver.WallTime(), 1), flush=True)
