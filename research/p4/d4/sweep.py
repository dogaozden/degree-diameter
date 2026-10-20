"""Sweep CP-SAT over many subgroup symmetries for the stand-in problem (mode st) at one q, and keep the best M.

usage: python sweep.py q secs_per_spec [--workers W] [--specs FILE | --random N] [--hint FILE] [--full SECS]
  --random N : N random cyclic subgroups of small order (2..12) of the spread stabiliser, plus all pairs of them.
  --full SECS: afterwards, solve the full model (no symmetry) with the best M so far as a hint.
Writes sols/sweep_st_q{q}.json (best M) and prints one line per spec.
"""
import argparse
import json
import random
import time
from collections import Counter
from pathlib import Path

from ortools.sat.python import cp_model

import groups
from w3k import W3, orbits

ap = argparse.ArgumentParser()
ap.add_argument('q', type=int)
ap.add_argument('secs', type=float)
ap.add_argument('--workers', type=int, default=1)
ap.add_argument('--specs', default=None)
ap.add_argument('--random', type=int, default=0)
ap.add_argument('--seed', type=int, default=1)
ap.add_argument('--hint', default=None)
ap.add_argument('--full', type=float, default=0)
ap.add_argument('--cap', type=int, default=2)
args = ap.parse_args()
q = args.q
W = W3(q)
n = len(W.pts)
here = Path(__file__).resolve().parent
outf = here / 'sols' / f'sweep_st_q{q}.json'
best = []
if outf.exists():
    best = json.loads(outf.read_text())['M']
if args.hint:
    h = json.loads(Path(args.hint).read_text())['M']
    if len(h) > len(best):
        best = h


def check(M):
    Ms = set(M)
    for j, L in enumerate(W.lines):
        c = sum(p in Ms for p in L)
        assert c <= (args.cap if W.is_spread_line[j] else 1)


def solve(gens, secs, hint=None):
    if gens:
        orbs, of = orbits(n, gens)
    else:
        orbs, of = [[i] for i in range(n)], list(range(n))
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f'x{k}') for k in range(len(orbs))]
    seen = set()
    for j, L in enumerate(W.lines):
        cnt = Counter(of[p] for p in L)
        key = (tuple(sorted(cnt.items())), W.is_spread_line[j])
        if key in seen:
            continue
        seen.add(key)
        m.Add(sum(c * x[o] for o, c in cnt.items()) <= (args.cap if W.is_spread_line[j] else 1))
    m.Maximize(sum(len(orbs[k]) * x[k] for k in range(len(orbs))))
    if hint:
        hs = set(hint)
        for k in range(len(orbs)):
            m.AddHint(x[k], all(p in hs for p in orbs[k]))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = secs
    s.parameters.num_workers = args.workers
    st = s.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return [], len(orbs), s.StatusName(st), s.BestObjectiveBound()
    M = sorted(p for k in range(len(orbs)) if s.Value(x[k]) for p in orbs[k])
    return M, len(orbs), s.StatusName(st), s.BestObjectiveBound()


def save(M, tag):
    global best
    check(M)
    if len(M) > len(best):
        best = M
        outf.write_text(json.dumps({'q': q, 'M': M, 'found_by': tag}))


specs = []
if args.specs:
    specs = [l.strip() for l in open(args.specs) if l.strip()]
rng = random.Random(args.seed)
rand_gens = []
if args.random:
    Q = q * q
    Fs = set(W.F[1:])
    tries = 0
    while len(rand_gens) < args.random and tries < 100000:
        tries += 1
        g = tuple(rng.randrange(Q) for _ in range(4))
        d = W.det(g)
        if d == 0 or d not in Fs:
            continue
        p = W.mat_perm(g)
        o = groups.perm_order(p)
        for target in (2, 3, 4, 5, 6, 8, 10, 12):
            if o % target == 0:
                pp = groups.power(p, o // target)
                rand_gens.append((f'rand{len(rand_gens)}(o{target})', [pp]))
                break
    pairs = []
    for i in range(len(rand_gens)):
        for k in range(i + 1, min(len(rand_gens), i + 4)):
            pairs.append((rand_gens[i][0] + '+' + rand_gens[k][0], rand_gens[i][1] + rand_gens[k][1]))
    rand_gens += pairs
t0 = time.time()
for spec in specs:
    M, no, st, bd = solve(groups.gens(W, spec), args.secs)
    print(f'{time.time() - t0:7.0f}s {spec:30s} orbits={no:5d} |M|={len(M):4d} {st} bound={bd}', flush=True)
    if M:
        save(M, spec)
for name, gens in rand_gens:
    _, of = orbits(n, gens)
    M, no, st, bd = solve(gens, args.secs)
    print(f'{time.time() - t0:7.0f}s {name:30s} orbits={no:5d} |M|={len(M):4d} {st} bound={bd}', flush=True)
    if M:
        save(M, name)
if args.full:
    M, no, st, bd = solve(None, args.full, hint=best)
    print(f'{time.time() - t0:7.0f}s FULL (hint {len(best)})        |M|={len(M):4d} {st} bound={bd}', flush=True)
    if M:
        save(M, 'full')
print('best', len(best))
