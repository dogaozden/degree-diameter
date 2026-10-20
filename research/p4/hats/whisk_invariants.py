"""Look for simple G-invariants of free points (G = <x3(s), x1(a)x5(-2a/c), tau>), to describe the q(q+1) orbits.
python3 whisk_invariants.py q"""
import itertools
import sys
from collections import defaultdict, Counter

import numpy as np

q = int(sys.argv[1])
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild', '--load']
src = open('hexbig_gf.py').read()
exec(compile(src.split('if build and okfree and okX:')[0], 'hexbig_gf.py', 'exec'))
GENS = [perms(kelem(0, 0, lam)) for lam in basis] + [perms(kelem(lam, 0, 0)) for lam in basis] + [(tp, tl)]
orb = {}
for p0 in free_pts:
    p0 = int(p0)
    if p0 in orb:
        continue
    o, fr = {p0}, [p0]
    while fr:
        nf = []
        for p in fr:
            for gp, gl in GENS:
                t = int(gp[p])
                if t not in o:
                    o.add(t)
                    nf.append(t)
        fr = nf
    for p in o:
        orb[p] = p0
reps = sorted(set(orb.values()))
print('free-point orbits:', len(reps))
# which coordinate patterns are constant on orbits
Pf = {p: P[p].tolist() for p in orb}
for i in range(7):
    zero_inv = all(len({Pf[p][i] == 0 for p in orb if orb[p] == r}) == 1 for r in reps)
    print('coordinate', i, 'zero-pattern invariant' if zero_inv else '')
for i, j in itertools.combinations(range(7), 2):
    ok = True
    vals = defaultdict(set)
    for p, r in orb.items():
        x = Pf[p]
        if x[j]:
            vals[r].add(int(MUL[x[i], INV[x[j]]]))
        else:
            vals[r].add(('inf', x[i] == 0))
    if all(len(s) == 1 for s in vals.values()):
        print('ratio x%d/x%d is invariant; values per orbit:' % (i, j), sorted(Counter(next(iter(s)) for s in vals.values()).items(), key=str))


# ratios of quadratic expressions: search pairs (f1, f2) among monomials and the binomial x2x3 - x4x5
mons = [(i, j) for i in range(7) for j in range(i, 7)]


def ev(x, m):
    if m == 'J':
        return int(ADD[MUL[x[2], x[3]], NEG[MUL[x[4], x[5]]]])
    i, j = m
    return int(MUL[x[i], x[j]])


cands = mons + ['J']
found = []
for m1 in cands:
    for m2 in cands:
        if m1 == m2:
            continue
        vals = defaultdict(set)
        for p, r in orb.items():
            x = Pf[p]
            a, b = ev(x, m1), ev(x, m2)
            vals[r].add(int(MUL[a, INV[b]]) if b else ('inf' if a else 'nan'))
        if all(len(s) == 1 for s in vals.values()):
            nv = len({next(iter(s)) for s in vals.values()})
            if nv > 2:
                found.append((nv, m1, m2))
found.sort(reverse=True)
print('invariant ratios with >2 values (values, num, den):', found[:15])
