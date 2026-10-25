"""viol.py FLAGS...: Hall violator of a flag set: X (points) with |N(X)| < |X|, and which flags' sets contain it."""
import sys, itertools
sys.path.insert(0, '.')
from obst import Geo
geo = Geo(); N = geo.N
fl = [tuple(map(int, t.split(':'))) for t in sys.argv[1:]]
size, mL, viol = geo.matching(fl, want_violator=True)
X, NX = viol
print('k', len(fl), 'matching', size, 'deficiency', N - size, '|X|', len(X), '|N(X)|', len(NX))
Xm = sum(1 << x for x in X); NXm = sum(1 << m for m in NX)
F = {p for p, l in fl}; Fl = {l for p, l in fl}
print('freed points in X:', [x for x in X if x in F], ' freed lines in N(X):', [m for m in NX if m in Fl])
for i, (p, l) in enumerate(fl):
    A, Ll, G, Pp = geo.flag_sets(p, l)
    print('flag', i, (p, l), '|X&A|', bin(Xm & A).count('1'), '|N(X)&Ll|', bin(NXm & Ll).count('1'),
          '|N(X)&G|', bin(NXm & G).count('1'), '|X&Pp|', bin(Xm & Pp).count('1'), 'X contains p?', p in X, 'N contains l?', l in NX)
for r in range(1, 4):
    for S in itertools.combinations(range(len(fl)), r):
        m = Xm
        for s in S: m &= geo.flag_sets(*fl[s])[0]
        cntA = bin(m).count('1')
        m2 = NXm
        for s in S: m2 &= geo.flag_sets(*fl[s])[1]
        cntL = bin(m2).count('1')
        if cntA >= 1 and (cntA > 0):
            print('S', S, 'X-points in all A_S:', cntA, ' N(X) in all Ll_S:', cntL)
