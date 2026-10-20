"""Build whisker sets from the hyperplane spreads S_z (z = (alpha, beta) != 0, hyperplane x0 + c x4 + alpha x2 +
beta x5 = 0) and a class function F (whiskers of S_z = its lines meeting S-lines with nu = F(z)), and test exactness.
python3 whisk_rule2.py q"""
import itertools
import sys
from collections import Counter

import numpy as np

q = int(sys.argv[1])
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild', '--load']
src = open('hexbig_gf.py').read()
exec(compile(src.split('if build and okfree and okX:')[0], 'hexbig_gf.py', 'exec'))
Slist = S.tolist()


def nu(x):
    x = [int(t) for t in x]
    I = int(ADD[MUL[x[2], x[3]], NEG[MUL[x[4], x[5]]]])
    D = int(ADD[MUL[c, MUL[x[2], x[2]]], MUL[x[5], x[5]]])
    return int(MUL[I, INV[D]]) if D else None


nu_line = {s: nu(P[lines[s][0]]) for s in Slist if s != v}
Sz = {}
for al, be in itertools.product(range(q), repeat=2):
    if not (al or be):
        continue
    av = np.array([1, 0, al, 0, c, be, 0])
    inH = fsum([MUL[P[:, i], av[i]] for i in range(7)]) == 0
    Sc = [int(k) for k in np.nonzero(inH[lines].all(axis=1))[0] if int(k) != v]
    assert len(Sc) == q ** 3
    Sz[(al, be)] = [(k, nu_line[int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]])]) for k in Sc]
freeset = set(int(p) for p in free_pts)
nu0 = 0  # E = S-lines with nu = 0 (any level works by the K_S symmetry)


def test(F):
    Wl = [k for z, lst in Sz.items() for k, nl in lst if nl == F(z)]
    cov = Counter(int(p) for k in Wl for p in lines[k] if int(p) in freeset)
    return len(Wl), len(cov) == len(freeset) and set(cov.values()) == {1}


good = []
for C1, C2 in itertools.product(range(1, q), repeat=2):
    F = lambda z, C1=C1, C2=C2: int(MUL[C1, z[0]]) if z[0] else int(MUL[C2, z[1]])
    n_, ok_ = test(F)
    if ok_:
        good.append((C1, C2))
print('F = C1*alpha (alpha != 0), C2*beta: exact for', good)
# linear F(z) = a*alpha + b*beta restricted where nonzero is impossible; try F = (a alpha^2 + b beta^2)/(alpha or beta)...
good2 = []
for a_, b_ in itertools.product(range(1, q), repeat=2):
    def F(z, a_=a_, b_=b_):
        num = int(ADD[MUL[a_, MUL[z[0], z[0]]], MUL[b_, MUL[z[1], z[1]]]])
        den = z[0] if z[0] else z[1]
        return int(MUL[num, INV[den]])
    n_, ok_ = test(F)
    if ok_:
        good2.append((a_, b_))
print('F = (a alpha^2 + b beta^2)/lead: exact for', good2)

reps = [(1, m) for m in range(q)] + [(0, 1)]


def make_F(vals):
    d = {}
    for (r, f) in zip(reps, vals):
        for lam in range(1, q):
            d[(int(MUL[lam, r[0]]), int(MUL[lam, r[1]]))] = int(MUL[lam, f])
    return lambda z: d[z]


allF = []
if q <= 5:
    for vals in itertools.product(range(1, q), repeat=q + 1):
        if test(make_F(vals))[1]:
            allF.append(vals)
print('all exact F (values F(1,0..q-1), F(0,1)):', allF)


def interp_ok(vals_m, top, deg):
    """Is m -> vals_m[m] (m in GF(q)) a polynomial of degree <= deg with m^deg coefficient top?"""
    for coeffs in itertools.product(range(q), repeat=deg):
        cs = list(coeffs) + [top]
        if all(int(fsum([MUL[cs[i], pw[m][i]] for i in range(deg + 1)])) == vals_m[m] for m in range(q)):
            return cs
    return None


pw = [[1] + [0] * 6 for _ in range(q)]
for m in range(q):
    x = 1
    pw[m] = []
    for i in range(7):
        pw[m].append(x)
        x = int(MUL[x, m])
for (a_, b_) in [(c, 1), (1, c)]:
    for vals in allF:
        Cm = [int(MUL[vals[m], ADD[MUL[a_, 1], MUL[b_, MUL[m, m]]]]) for m in range(q)]
        top = int(MUL[vals[q], b_])
        print('Q = %d a^2 + %d b^2:' % (a_, b_), vals, '-> cubic', interp_ok(Cm, top, 3))

# cubic ansatz: F = C / (alpha^2 + c beta^2), C = c0 a^3 + c1 a^2 b + c2 a b^2 + c3 b^3
cubic_ok = []
for cs in itertools.product(range(q), repeat=4):
    def Cv(z, cs=cs):
        a_, b_ = z
        return int(fsum([MUL[cs[0], MUL[a_, MUL[a_, a_]]], MUL[cs[1], MUL[a_, MUL[a_, b_]]],
                         MUL[cs[2], MUL[a_, MUL[b_, b_]]], MUL[cs[3], MUL[b_, MUL[b_, b_]]]]))
    if any(Cv(z) == 0 for z in Sz):
        continue
    F = lambda z, Cv=Cv: int(MUL[Cv(z), INV[ADD[MUL[z[0], z[0]], MUL[c, MUL[z[1], z[1]]]]]])
    if test(F)[1]:
        cubic_ok.append(cs)
print('q=%d c=%d: exact cubics C (c0..c3):' % (q, c), cubic_ok)
