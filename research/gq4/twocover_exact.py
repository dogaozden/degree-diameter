"""Symmetry-reduced search for a 2-cover of Q(4,q) by lines (every point on at most 2 chosen lines, a line may be
chosen twice). An exact 2-cover has 2(q^2+1) lines.

Take a group G of isometries of the quadric (drawn from sym_spread.py's generators). A G-invariant multiset is a
choice of multiplicities x_O in {0,1,2} for the G-orbits O on lines. The problem becomes an integer program:
    maximise sum_O |O| x_O   subject to   for each point p: sum_O (lines of O through p) x_O <= 2,   x_O in {0,1,2}.
Solved by HiGHS (scipy milp) with a time limit. An optimum of 2(q^2+1) is an exact 2-cover. Otherwise the answer is
extended greedily by single lines whose points still have load < 2, and re-checked.

usage: python3 twocover_exact.py q trials seconds_per_ilp [seed] [workers] [cap]
  cap: largest group order (on points) allowed, default 170.
writes: spreads/cover2_q{q}_t{size}.json (a JSON list of line indices into q4(q)'s lines; a repeated index means the
line is chosen twice) when the best size of this run beats every cover2 file already in spreads/ for that q.
"""
import glob
import json
import random
import re
import sys
import time
from multiprocessing import get_context
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sym_spread as ss  # noqa: E402
from gq_clones import lib, q4  # noqa: E402


def check_cover2(lines, multiset):
    """Independent check: indices in range, every point on at most 2 chosen lines (repeats count)."""
    assert all(0 <= k < len(lines) for k in multiset), 'line index out of range'
    count = {}
    for k in multiset:
        for p in lines[k]:
            count[p] = count.get(p, 0) + 1
    return max(count.values(), default=0) <= 2


def fill(chosen, lines, rng):
    """Greedily add lines (or second copies) whose points all have load < 2."""
    load = {}
    for k in chosen:
        for p in lines[k]:
            load[p] = load.get(p, 0) + 1
    out = list(chosen)
    order = list(range(len(lines)))
    rng.shuffle(order)
    for k in order:
        while all(load.get(p, 0) < 2 for p in lines[k]):
            out.append(k)
            for p in lines[k]:
                load[p] = load.get(p, 0) + 1
    return out


def trial(args):
    t, secs, cap, seed = args
    lines, P = ss.S['lines'], len(ss.S['pts'])
    rng = random.Random(seed * 1000003 + t)
    kind = rng.choice(ss.KINDS)
    gens = ss.candidate(kind, rng, cap)
    if gens is None:
        return None
    n = ss.group_order(gens, cap)
    if n is None or n < 2:
        return None
    line_perms = [np.array([ss.S['line_idx'][frozenset(int(s[p]) for p in L)] for L in lines]) for s in gens]
    orbs = ss.orbits(line_perms, len(lines))
    rows, cols = [], []
    w = np.zeros(len(orbs))
    for c, O in enumerate(orbs):
        w[c] = len(O)
        for j in O:
            for p in lines[j]:
                rows.append(p)
                cols.append(c)
    # Each (point, orbit) pair appears once per line of the orbit through that point, so duplicates are counts.
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(P, len(orbs)))
    res = milp(c=-w, constraints=LinearConstraint(A, -np.inf, 2), integrality=np.ones(len(orbs)),
               bounds=Bounds(0, 2), options={'time_limit': secs, 'disp': False})
    if res.x is None:
        ilp, chosen, bound, status = 0, [], None, res.status
    else:
        x = np.rint(res.x).astype(int)
        chosen = [j for c, O in enumerate(orbs) for j in O for _ in range(x[c])]
        ilp = len(chosen)
        bound = getattr(res, 'mip_dual_bound', None)
        bound = None if bound is None else -bound  # scipy reports the bound of the minimised objective
        status = res.status
    chosen = fill(chosen, lines, rng)
    assert check_cover2(lines, chosen), 'internal error: cover violates the cap'
    return dict(t=t, kind=kind, order=n, orbits=len(orbs), ilp=ilp, bound=bound, status=status,
                size=len(chosen), lines=sorted(chosen))


def existing_best(q):
    best = 0
    for f in glob.glob(str(HERE / 'spreads' / f'cover2_q{q}_t*.json')):
        m = re.search(r'_t(\d+)\.json$', f)
        if m:
            best = max(best, int(m.group(1)))
    return best


def main():
    q = int(sys.argv[1])
    trials = int(sys.argv[2])
    secs = float(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 5
    cap = int(sys.argv[6]) if len(sys.argv) > 6 else 170
    t0 = time.time()
    F = lib.GF(q)
    pts, lines, ovoid = q4(q)
    ss.S.update(q=q, F=F, pts=pts, lines=lines, idx={p: i for i, p in enumerate(pts)},
                line_idx={L: k for k, L in enumerate(lines)})
    bound = 2 * (q * q + 1)
    print(f'q={q}: {len(pts)} points, {len(lines)} lines, exact bound {bound}; trials={trials} ilp_secs={secs} '
          f'cap={cap} workers={workers}; current best cover2 file: {existing_best(q)} ({time.time() - t0:.1f}s setup)',
          flush=True)

    best = None
    done = 0
    with get_context('fork').Pool(workers) as pool:
        for r in pool.imap_unordered(trial, [(t, secs, cap, seed) for t in range(trials)]):
            done += 1
            if r is None:
                continue
            bnd = '' if r['bound'] is None else f" bound={r['bound']:.1f}"
            print(f"[{done}/{trials}] t={r['t']} {r['kind']} |G|={r['order']} orbits={r['orbits']} ilp={r['ilp']}{bnd} "
                  f"status={r['status']} -> size {r['size']} ({time.time() - t0:.0f}s)", flush=True)
            if best is None or r['size'] > best['size']:
                best = r

    if best is None:
        print('no usable trial', flush=True)
        return
    assert check_cover2(lines, best['lines'])
    print(f"BEST q={q}: size {best['size']} (exact={best['size'] == bound}) from t={best['t']} {best['kind']} "
          f"|G|={best['order']} ({time.time() - t0:.0f}s)", flush=True)
    prev = existing_best(q)
    if best['size'] > prev:
        out = HERE / 'spreads' / f"cover2_q{q}_t{best['size']}.json"
        out.write_text(json.dumps(best['lines']))
        print(f'saved {out} (checked; previous best {prev})', flush=True)
    else:
        print(f'not saved: does not beat the existing best {prev}', flush=True)


if __name__ == '__main__':
    main()
