"""Exact searches (OR-Tools CP-SAT) for point sets M of W(3,q) relative to the regular spread S.

modes:
  po  : partial ovoid: every t.i. line has <= 1 point of M.
  st  : stand-ins at Delta = q+2: lines outside S <= 1, lines of S <= cap (default 2).
  free: lines outside S <= 1, lines of S unrestricted (the j = 3 relaxation).
Optional symmetry: --sym NAME restricts M to unions of orbits of a subgroup (see groups.py).

usage: python cp_m.py q mode seconds [--cap 2] [--sym name] [--hint file]
"""
import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model

from w3k import W3, orbits

ap = argparse.ArgumentParser()
ap.add_argument('q', type=int)
ap.add_argument('mode')
ap.add_argument('secs', type=float)
ap.add_argument('--cap', type=int, default=2)
ap.add_argument('--sym', default=None)
ap.add_argument('--workers', type=int, default=2)
ap.add_argument('--lb', type=int, default=0)
ap.add_argument('--out', default=None)
args = ap.parse_args()
q = args.q
W = W3(q)
n = len(W.pts)
if args.sym:
    import groups
    gens = groups.gens(W, args.sym)
    orbs, orb_of = orbits(n, gens)
else:
    orbs = [[i] for i in range(n)]
    orb_of = list(range(n))
print(f'q={q} mode={args.mode} sym={args.sym} orbits={len(orbs)} sizes={sorted(set(map(len, orbs)))}', flush=True)
m = cp_model.CpModel()
x = [m.NewBoolVar(f'x{k}') for k in range(len(orbs))]
seen = set()
for j, L in enumerate(W.lines):
    cnt = {}
    for p in L:
        cnt[orb_of[p]] = cnt.get(orb_of[p], 0) + 1
    key = (tuple(sorted(cnt.items())), W.is_spread_line[j])
    if key in seen:
        continue
    seen.add(key)
    if W.is_spread_line[j]:
        if args.mode == 'po':
            cap = 1
        elif args.mode == 'st':
            cap = args.cap
        else:
            continue
    else:
        cap = 1
    m.Add(sum(c * x[o] for o, c in cnt.items()) <= cap)
obj = sum(len(orbs[k]) * x[k] for k in range(len(orbs)))
if args.lb:
    m.Add(obj >= args.lb)
m.Maximize(obj)
s = cp_model.CpSolver()
s.parameters.max_time_in_seconds = args.secs
s.parameters.num_workers = args.workers
t0 = time.time()
st = s.Solve(m)
M = sorted(p for k in range(len(orbs)) if s.Value(x[k]) for p in orbs[k]) if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else []
print(f'status={s.StatusName(st)} |M|={len(M)} bound={s.BestObjectiveBound()} time={time.time()-t0:.1f}s', flush=True)
if M:
    # check
    Ms = set(M)
    for j, L in enumerate(W.lines):
        c = sum(p in Ms for p in L)
        if W.is_spread_line[j]:
            assert args.mode != 'po' or c <= 1
            assert args.mode != 'st' or c <= args.cap
        else:
            assert c <= 1
    sc = [sum(p in Ms for p in L) for L in W.spread]
    print('spread line counts:', {k: sc.count(k) for k in sorted(set(sc))})
    if args.out:
        Path(args.out).write_text(json.dumps({'q': q, 'mode': args.mode, 'sym': args.sym, 'M': M}))
