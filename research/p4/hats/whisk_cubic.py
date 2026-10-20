"""Explicit whisker rule: W = union over z = (alpha, beta) != 0 of the lines of the Hermitian spread S_z (lines of H(q)
in x0 + c x4 + alpha x2 + beta x5 = 0) that meet an S-line with nu = F(z), where
  nu(x) = (x2 x3 - x4 x5) / (c x2^2 + x5^2),   F(z) = c0 alpha + c1 beta - beta^3 / (alpha^2 + c beta^2).
Tests exactness for all (c0, c1) (or given ones).  python3 whisk_cubic.py q [c0,c1]"""
import itertools
import sys
from collections import Counter

import numpy as np

q = int(sys.argv[1])
want = [tuple(int(t) for t in sys.argv[2].split(','))] if len(sys.argv) > 2 else None
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild']
src = open('hexbig_gf.py').read()
exec(compile(src.split('free_pts = np.nonzero((Sline_of < 0)')[0], 'hexbig_gf.py', 'exec'))
Slist = S.tolist()
free_pts = np.nonzero((Sline_of < 0) & (dist[:N] == 5))[0]
freeset = set(int(p) for p in free_pts)


def nu(x):
    x = [int(t) for t in x]
    I = int(ADD[MUL[x[2], x[3]], NEG[MUL[x[4], x[5]]]])
    D = int(ADD[MUL[c, MUL[x[2], x[2]]], MUL[x[5], x[5]]])
    return int(MUL[I, INV[D]]) if D else None


nu_line = {s: nu(P[lines[s][0]]) for s in Slist if s != v}
assert all(len({nu(P[p]) for p in lines[s]}) == 1 for s in Slist if s != v), 'nu not constant on S-lines'
Sz = {}
for al, be in itertools.product(range(q), repeat=2):
    if not (al or be):
        continue
    inH = fsum([P[:, 0], MUL[c, P[:, 4]], MUL[al, P[:, 2]], MUL[be, P[:, 5]]]) == 0
    Sc = [int(k) for k in np.nonzero(inH[lines].all(axis=1))[0] if int(k) != v]
    assert len(Sc) == q ** 3, (al, be, len(Sc))
    Sz[(al, be)] = [(k, nu_line[int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]])]) for k in Sc]
log('spreads S_z built:', len(Sz))


def Fz(z, c0, c1):
    al, be = z
    Q = int(ADD[MUL[al, al], MUL[c, MUL[be, be]]])
    return int(ADD[ADD[MUL[c0, al], MUL[c1, be]], NEG[MUL[MUL[be, MUL[be, be]], INV[Q]]]])


good = []
for c0, c1 in (want or itertools.product(range(q), repeat=2)):
    if any(Fz(z, c0, c1) == 0 for z in Sz):
        continue
    Wl = [k for z, lst in Sz.items() for k, nl in lst if nl == Fz(z, c0, c1)]
    cov = Counter(int(p) for k in Wl for p in lines[k] if int(p) in freeset)
    exact = len(Wl) == q * q * (q * q - 1) and len(cov) == len(freeset) and set(cov.values()) == {1}
    if exact:
        good.append((c0, c1))
        if len(good) == 1:
            (HERE / f'whiskers_rule_q{q}.json').write_text(json.dumps({'q': q, 'c': c, 'v': v, 'S': Slist,
                                                                       'whiskers': sorted(Wl), 'c0c1': [c0, c1]}))
log(f'q={q} c={c}: exact (c0, c1):', good, f'({len(good)} of {q*q})')
