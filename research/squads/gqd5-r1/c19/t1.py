import time, sys, numpy as np, ctypes
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c19')
from common import *
from common import _lib
G = gqlib.Q4(5)
rng = np.random.default_rng(3)
for r in (2,3):
    g = Graph(G, r)
    for trial in range(3):
        M = {t: rng.permutation(G.np) for t in g.trans}
        R = {(0,1): set(rng.choice(G.np, 10, replace=False).tolist())}
        eu, ev = g.edges(M, R)
        t0=time.time(); b1 = _lib.count_bad_bits(g.n, len(eu), eu.ctypes.data, ev.ctypes.data, 5, None); t1=time.time()
        b2 = _lib.count_bad(g.n, len(eu), eu.ctypes.data, ev.ctypes.data, 5, None); t2=time.time()
        print(r, b1, b2, 'bits %.4f  plain %.4f' % (t1-t0, t2-t1))
        assert b1==b2
    # per-vertex check
    b, pv = count_bad(g.n, eu, ev, 5, per=True); print('per sum', pv.sum(), b)
