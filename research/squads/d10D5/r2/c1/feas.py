#!/usr/bin/env python3
"""feas.py GQBIN SEED TRIES M MAXEL: find elements h of order M with all POINT cycles of length M (random PGSp(4,7)
elements, power trick), keep valid flag orbits (size M, distinct points and lines), test each orbit on its own with the
exact-coverage matching (sym.Matcher). Prints feasible orbits; writes feas_M_SEED.txt lines 'pt:ln ...'.
usage: python3 -I feas.py gq/gq_q7.bin SEED TRIES M MAXEL"""
import sys, random, math, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; seed = int(sys.argv[2]); tries = int(sys.argv[3]); M = int(sys.argv[4]); maxel = int(sys.argv[5])
rng = random.Random(seed)
q, N, lines, lof, coords = load_all(fn)
index = {c: i for i, c in enumerate(coords)}
lidx = {frozenset(ps): l for l, ps in enumerate(lines)}
flags_all = [(p, l) for l in range(len(lines)) for p in lines[l]]
Mt = Matcher(q, N, lines, lof)
def pcomp(a, b): return [a[b[i]] for i in range(len(b))]
def ppow(a, e):
    r = list(range(len(a))); base = a[:]
    while e:
        if e & 1: r = pcomp(base, r)
        base = pcomp(base, base); e >>= 1
    return r
def porder(a): return math.lcm(*cycle_type(a).keys())
els = []; seenel = set()
for t in range(tries):
    if len(els) >= maxel: break
    Mx = random_elem(rng)
    pp = perm_points(Mx, coords, index)
    o = porder(pp)
    if o % M: continue
    h = ppow(pp, o // M)
    if cycle_type(h) != {M: N // M}: continue
    key = tuple(h)
    if key in seenel: continue
    seenel.add(key); els.append(h)
print('semiregular-on-points order', M, 'elements', len(els), flush=True)
out = open(f'feas_{M}_{seed}.txt', 'w')
for ei, h in enumerate(els):
    pl = perm_lines(h, lines, lidx)
    orbs = flag_orbits(h, pl, flags_all)
    valid = [ob for ob in orbs if len(ob) == M and len({p for p, _ in ob}) == M and len({l for _, l in ob}) == M]
    t0 = time.time(); feas = []
    for ob in valid:
        sz, _ = Mt.size(ob)
        if sz == N: feas.append(ob)
    print('EL', ei, 'lines cycles', sorted(cycle_type(pl).items()), 'valid orbits', len(valid), 'feasible single', len(feas),
          'time %.1f' % (time.time() - t0), flush=True)
    for ob in feas:
        out.write(' '.join(f'{p}:{l}' for p, l in ob) + '\n')
    out.flush()
    if feas:
        # also keep h for later
        pass
out.close()
