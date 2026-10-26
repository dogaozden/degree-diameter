import sys, pickle, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, slots2
from grid import REQ
n = int(sys.argv[1])
d = pickle.load(open('res_%d.pkl' % n, 'rb'))
P, best, fa, T, types = d['P'], d['best'], d['forms_at'], d['tournaments'], d['types']
tida, typa = d['tida'], d['typa']
# recover witness: global index -> tournament & typing
def wit(gi):
    arcs, typ = slots2.describe(T, n, tida, typa, types, gi)
    return typ, arcs
def fstr(f):
    s = []
    for x, name in zip(f, 'abc'):
        if x: s.append(('%d' % x if x != 1 else '') + name)
    return '+'.join(s) if s else '0'
print('n=%d (r=%d) grid points %d' % (n, (n-1)//2, len(P)))
for g in range(len(P)):
    if tuple(int(x) for x in P[g]) in REQ:
        fl = sorted(fa[g].keys())
        print('  point', tuple(int(x) for x in P[g]), 'best', round(best[g], 3),
              'formulas', [fstr(f) for f in fl][:8], 'witness typing', wit(fa[g][fl[0]])[0])
# region map: formula -> grid points where it attains the best
reg = collections.defaultdict(list)
for g in range(len(P)):
    for f in fa[g]:
        reg[f].append(g)
# report formulas attaining the max on the most grid points, with the range of b/a and c/a
print(' distinct formulas attaining max somewhere:', len(reg))
for f, gs in sorted(reg.items(), key=lambda kv: -len(kv[1]))[:12]:
    pts = [tuple(int(x) for x in P[g]) for g in gs]
    bs = [p[1] for p in pts]; cs = [p[2] for p in pts]
    print('  %-12s on %3d pts, b in [%d,%d], c in [%d,%d]' % (fstr(f), len(gs), min(bs), max(bs), min(cs), max(cs)))
