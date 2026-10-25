#!/usr/bin/env python3
"""single.py: for semiregular elements g (points cycles all of one length m), test every <g>-orbit of flags on its own
(perfect matching?), then random pairs/triples of feasible orbits.  usage: python3 -I single.py gq/gq_q7.bin SEED M NEL"""
import sys, random, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; seed = int(sys.argv[2]); m = int(sys.argv[3]); nel = int(sys.argv[4])
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
Mt = Matcher(q, N, lines, lof)
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]
found = []
tried = set()
for e in range(200000):
    if len(tried) >= nel: break
    Mx = random_elem(rng)
    pp = perm_points(Mx, coords, index)
    ct = cycle_type(pp)
    if order_of(ct) != m or ct != {m: N // m}: continue
    key = tuple(sorted(pp)) and tuple(pp)
    h = hash(key)
    if h in tried: continue
    tried.add(h)
    pl = perm_lines(pp, lines, lidx)
    orbs = flag_orbits(pp, pl, flags_all)
    assert all(len(o) == m for o in orbs)
    t0 = time.time(); feas = []
    for oi, ob in enumerate(orbs):
        sz, _ = Mt.size(ob)
        if sz == N: feas.append(oi)
    print('ELEM', len(tried), 'order', m, 'orbits', len(orbs), 'feasible singles', len(feas), 'time %.1f' % (time.time() - t0), flush=True)
    if feas:
        # pairs / larger unions of feasible orbits, random greedy
        best = 0; bestflags = None
        for trial in range(40):
            order = feas[:]; rng.shuffle(order)
            cur = []; FP = set(); FL = set()
            for oi in order:
                ob = orbs[oi]; ps = {p for p, _ in ob}; ls = {l for _, l in ob}
                if ps & FP or ls & FL: continue
                cand = cur + ob
                sz, _ = Mt.size(cand)
                if sz == N: cur = cand; FP |= ps; FL |= ls
            if len(cur) > best: best = len(cur); bestflags = cur
            print('   trial', trial, 'k', len(cur), flush=True) if trial < 3 else None
        print('   BEST k', best, 'flags', bestflags, flush=True)
        found.append((best, bestflags))
print('SUMMARY', [b for b, _ in found])
