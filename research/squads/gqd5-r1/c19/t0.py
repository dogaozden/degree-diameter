import time, random, numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c19')
from common import *
G = gqlib.Q4(5); print(G.name, G.np, G.nl)
for r in (2, 3):
    g = Graph(G, r)
    rng = np.random.default_rng(1)
    M = {t: rng.permutation(G.np) for t in g.trans}
    t0 = time.time(); b = g.bad(M, {}); print('r', r, 'n', g.n, 'bad R=empty', b, 'time', time.time() - t0)
    t0 = time.time(); b = g.bad(M, {}); print('time again', time.time()-t0)
