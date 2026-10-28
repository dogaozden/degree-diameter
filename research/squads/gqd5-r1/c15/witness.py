import sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, slots2
from grid import REQ
def fstr(f):
    s = []
    for x, name in zip(f, 'abc'):
        if x: s.append(('%d' % x if x != 1 else '') + name)
    return '+'.join(s) if s else '0'
n = int(sys.argv[1])
d = pickle.load(open('res_%d.pkl' % n, 'rb'))
P, T, types, tida, typa, fa, best = d['P'], d['tournaments'], d['types'], d['tida'], d['typa'], d['forms_at'], d['best']
for g in range(len(P)):
    if tuple(int(x) for x in P[g]) in REQ:
        pt = tuple(int(x) for x in P[g])
        fl = sorted(fa[g].keys())
        print(pt, 'best', int(round(best[g])), 'formulas:', ' | '.join(fstr(f) for f in fl))
        gi = fa[g][fl[0]]
        A = T[tida[gi]]
        typ = ''.join('HD'[x] for x in types[typa[gi]])
        outs = [[int(v) for v in range(n) if A[u, v]] for u in range(n)]
        print('   typing', typ, ' out-lists', outs)
