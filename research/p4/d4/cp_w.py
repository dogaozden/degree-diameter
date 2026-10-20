"""Weighted m-ovoids of W(3,q) (dually weighted m-covers of Q(4,q)), and the stand-in relaxation for odd j.

mode 'ovoid': w: points -> {0..wmax}, every t.i. line has weight exactly m (feasibility).
mode 'st'   : every t.i. line outside S has weight <= m, every line of S <= m(m+1); maximise sum w.
  (Stand-ins at Delta = q+1+m: a point of Q(4,q) on the ovoid has 1+m stand-ins, each serving m line copies.)
--sym SPEC: w constant on orbits of a subgroup (groups.py).
usage: cp_w.py q m secs [--mode ovoid|st] [--wmax K] [--sym SPEC] [--workers 1]
"""
import argparse
import json
import time
from collections import Counter

from ortools.sat.python import cp_model

from w3k import W3, orbits

ap = argparse.ArgumentParser()
ap.add_argument('q', type=int)
ap.add_argument('m', type=int)
ap.add_argument('secs', type=float)
ap.add_argument('--mode', default='ovoid')
ap.add_argument('--wmax', type=int, default=None)
ap.add_argument('--sym', default=None)
ap.add_argument('--workers', type=int, default=1)
ap.add_argument('--out', default=None)
args = ap.parse_args()
q, j = args.q, args.m
W = W3(q)
n = len(W.pts)
if args.sym:
    import groups
    orbs, of = orbits(n, groups.gens(W, args.sym))
else:
    orbs, of = [[i] for i in range(n)], list(range(n))
wmax = args.wmax if args.wmax is not None else j
mdl = cp_model.CpModel()
w = [mdl.NewIntVar(0, wmax, f'w{k}') for k in range(len(orbs))]
seen = set()
for k, L in enumerate(W.lines):
    cnt = Counter(of[p] for p in L)
    key = (tuple(sorted(cnt.items())), W.is_spread_line[k])
    if key in seen:
        continue
    seen.add(key)
    expr = sum(c * w[o] for o, c in cnt.items())
    if args.mode == 'ovoid':
        mdl.Add(expr == j)
    else:
        mdl.Add(expr <= (j * (j + 1) if W.is_spread_line[k] else j))
if args.mode == 'st':
    mdl.Maximize(sum(len(orbs[k]) * w[k] for k in range(len(orbs))))
s = cp_model.CpSolver()
s.parameters.max_time_in_seconds = args.secs
s.parameters.num_workers = args.workers
t0 = time.time()
st = s.Solve(mdl)
res = f'q={q} m={j} mode={args.mode} sym={args.sym} orbits={len(orbs)} {s.StatusName(st)} time={time.time() - t0:.1f}s'
if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    wp = [s.Value(w[of[p]]) for p in range(n)]
    res += f' sum={sum(wp)} target={j * (q * q + 1)} weights={dict(sorted(Counter(wp).items()))}'
    res += f' S-sums={dict(Counter(sum(wp[p] for p in L) for L in W.spread))}'
    for k, L in enumerate(W.lines):  # independent check
        tot = sum(wp[p] for p in L)
        if args.mode == 'ovoid':
            assert tot == j
        else:
            assert tot <= (j * (j + 1) if W.is_spread_line[k] else j)
    if args.out:
        with open(args.out, 'w') as f:
            json.dump({'q': q, 'm': j, 'mode': args.mode, 'sym': args.sym, 'w': wp}, f)
print(res, flush=True)
