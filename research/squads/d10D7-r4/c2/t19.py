# c2: exact max clique over T_m orbits (m given), then map to points
import numpy as np, sys, time
from orb import orbit_graph
from mc import max_clique
from gf import NP
m = int(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 600
t0 = time.time()
SC, A = orbit_graph(m)
print('m', m, 'self-compat orbits', len(SC), 'density', A.sum() / max(1, len(SC) * (len(SC) - 1)), 'deg mean', A.sum(1).mean(), flush=True)
cl, sz, complete, nodes = max_clique(A, time_limit=tl)
print('max clique orbits', sz, 'complete', complete, 'nodes', nodes, 'points', sz * m, 'time %.1f' % (time.time() - t0), flush=True)
pts = sorted(int((SC[c] + j * (NP // m)) % NP) for c in cl for j in range(m))
np.save('T%d_clique_L.npy' % m, np.array(pts, dtype=np.int64))
print('saved classes', len(pts))
