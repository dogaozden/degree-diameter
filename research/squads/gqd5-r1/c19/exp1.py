import time, sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c19')
from common import *
G = gqlib.Q4(5); D5 = repair.full_dist(G)
rng = np.random.default_rng(7)
for r in (2, 3):
    g = Graph(G, r)
    t0 = (0, 1)
    print('== r=%d levels=%d' % (r, g.L))
    for s in (1, 2, 3, 5, 8, 12, 20, 30, 50, 80):
        for trial in range(3):
            M = {t: rng.permutation(G.np) for t in g.trans}
            R = {t0: set(rng.choice(G.np, s, replace=False).tolist())}
            bw = g.bad(M, R)
            # two-level count: source level 0 (H), target level 1 (H)
            bt = repair.brute_bad(G, 'H', 'H', M[t0], R[t0], D5)
            ok, fails = repair.exact_conditions(G, 'H', 'H', M[t0], R[t0])
            print('s=%3d trial=%d  whole=%7d  two-level=%7d  E-ok=%s %s' % (s, trial, bw, bt, ok, [f[0] for f in fails][:4]))
            sys.stdout.flush()
