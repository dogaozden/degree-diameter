import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/bcd-d8-r1/c6')
import base2 as b
rng = np.random.default_rng(int(sys.argv[2]))
M = int(sys.argv[1])
pi = b.equiv_perm(b.H.porb, b.H.ppos, b.H.prep, rng, b.TP)
rho = b.equiv_perm(b.H.lorb, b.H.lpos, b.H.lrep, rng, b.TL)
E, inv, nk = b.build_edges(pi, rho)
print('edges', len(E), 'keys', nk, 'orbits', len(b.BREP))
w = rng.integers(0, M, nk)
p = f'{b.HERE}/t0_{M}_{sys.argv[2]}.spec'
b.write_spec(p, M, E, inv, w)
t = time.time(); c = b.cost(p); print('M', M, 'cost', c, 'time', round(time.time()-t, 2))
