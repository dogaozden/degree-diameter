"""For free points p: along the affine line A_p = {z : alpha p2 + beta p5 = -L(p)}, the S_z-line through p meets an
S-line with nu = phi_p(z). Look at phi_p(z) - beta... to find its form.  python3 whisk_phi.py q"""
import itertools
import sys
from collections import Counter

import numpy as np

q = int(sys.argv[1])
sys.argv = ['whisk_cubic.py', str(q), '1,0']
src = open('whisk_cubic.py').read()
exec(compile(src.split('def Fz(')[0], 'whisk_cubic.py', 'exec'))
zline = {}
for z, lst in Sz.items():
    for k, nl in lst:
        zline[k] = (z, nl)
rows = []
for p in list(free_pts)[:200]:
    p = int(p)
    x = [int(t) for t in P[p]]
    Lp = int(ADD[x[0], MUL[c, x[4]]])
    data = {}
    for k in through[p]:
        k = int(k)
        if k in zline:
            z, nl = zline[k]
            assert int(fsum([MUL[z[0], x[2]], MUL[z[1], x[5]], Lp])) == 0
            data[z] = nl
    rows.append((x, Lp, data))
# test: is phi_p(z) = nu(p) + (something)?  print a few
for x, Lp, data in rows[:3]:
    print('p', x, 'nu(p) =', nu(x), 'L =', Lp, ' phi:', sorted(data.items()))

# H_p(z) = phi_p(z) + beta^3 / Q(z) along A_p; normalize p so that L(p) = 1 and parametrize z = z0 + s (p5, -p2)
def Qf(z):
    return int(ADD[MUL[z[0], z[0]], MUL[c, MUL[z[1], z[1]]]])


res = Counter()
table = {}
for p in free_pts:
    p = int(p)
    x = [int(t) for t in P[p]]
    Lp = int(ADD[x[0], MUL[c, x[4]]])
    x = [int(MUL[INV[Lp], t]) for t in x]  # now L = 1
    data = {}
    for k in through[p]:
        k = int(k)
        if k in zline:
            z, nl = zline[k]
            data[z] = int(ADD[nl, MUL[MUL[z[1], MUL[z[1], z[1]]], INV[Qf(z)]]])
    d = (x[5], int(NEG[x[2]]))
    z0 = next(iter(data))
    Hs = {}
    for s in range(q):
        z = (int(ADD[z0[0], MUL[s, d[0]]]), int(ADD[z0[1], MUL[s, d[1]]]))
        Hs[s] = data[z]
    slope = int(ADD[Hs[1], NEG[Hs[0]]])
    affine = all(Hs[s] == int(ADD[Hs[0], MUL[s, slope]]) for s in range(q))
    res[affine] += 1
    table.setdefault((x[2], x[5]), set()).add(slope)
print('H_p affine along A_p for all free p:', dict(res))
print('slope determined by (p2, p5) (L(p)=1)?', all(len(s) == 1 for s in table.values()))
for key in sorted(table)[:12]:
    print('  (p2,p5) =', key, ' slope', table[key])
