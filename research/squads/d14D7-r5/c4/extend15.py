#!/usr/bin/env python3
"""c4: extend the order-15 torus group of the 756 set, h = (4,2,4,0) in T(E,H,H,L), by involutions n = w*t of N(T)
that normalise <h>.  G = <h, n> has order 30 (dihedral-type) and contains <h>, so its invariant sets are a subset of
the <h>-invariant sets.  Each distinct G is run through orbclq (-t given).
usage: extend15.py [--t 15] [--max 6] [--seed 1]"""
import sys, os, json, random, argparse, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import normext as N
import numpy as np
import hashlib

ap = argparse.ArgumentParser()
ap.add_argument('--t', type=float, default=15)
ap.add_argument('--max', type=int, default=6)
ap.add_argument('--seed', type=int, default=1)
a = ap.parse_args()

T = N.Torus(['E', 'H', 'H', 'L'])
h_exp = (4, 2, 4, 0)
hi = T.index[h_exp]
h = T.elems[hi]
Hk = set(N.closure([h], limit=100).keys())
print('order of h:', len(Hk), flush=True)
invs = []
for w in T.Wlist[1:]:
    if not (N.mm(w, w) == N.I7).all():
        continue
    for ti, tm in enumerate(T.elems):
        nm = N.mm(w, tm)
        if (N.mm(nm, nm) == N.I7).all() and all(N.key(N.mm(N.mm(nm, x), nm)) in Hk for x in [h]):
            invs.append((T.Wnames[N.key(w)], ti, nm))
print('involutions normalising <h>:', len(invs), flush=True)
rng = random.Random(a.seed)
rng.shuffle(invs)
seen = set()
results = []
for widx, ti, nm in invs:
    G = N.closure([h, nm], limit=200)
    if G is None:
        continue
    dig = hashlib.sha1(b''.join(sorted(G.keys()))).hexdigest()[:16]
    if dig in seen:
        continue
    seen.add(dig)
    name = f'ext15_w{widx}_t{ti}_o{len(G)}'
    gens_block = [h, nm]
    gens_std = [T.to_std(M) for M in gens_block]
    gpath = os.path.join(N.GENS, name + '.txt')
    N.L.write_gens(gpath, [M.tolist() for M in gens_std], f'c4 extend15: <h> + involution, |G|={len(G)}')
    outp = os.path.join(N.SETS, name + '.txt')
    t0 = time.time()
    res, rc, err = N.run_orbclq(gpath, outp, a.t, a.seed)
    best = int(res.get('best', 0))
    rec = dict(name=name, types=['E', 'H', 'H', 'L'], H=[list(h_exp)], weyl=[widx], tdesc=[list(T.exps[ti])],
               order=len(G), K=res.get('good'), best=best, exact=res.get('exact'),
               pairs_orthogonal=res.get('pairs_orthogonal'), rc=rc, wall=round(time.time() - t0, 1))
    with open(N.RUNS, 'a') as f:
        f.write(json.dumps(rec) + '\n')
    print(f"{name} |G|={len(G)} K={res.get('good')} best={best} exact={res.get('exact')} rc={rc}", flush=True)
    if best < 740 and os.path.exists(outp):
        os.remove(outp)
    results.append(best)
    if len(results) >= a.max:
        break
print('done; bests', results, flush=True)
