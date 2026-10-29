import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c1')
import numpy as np
from search import tabu_indep
z = np.load('/home/user/degree-diameter/research/squads/conics2-r1/c1/cache_q5.npz')
C = (z['pc'] | z['d4'])          # points conflict unless opposite
N = C.shape[0]
verts = np.arange(N)
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
best = None
t0 = time.time()
s = int(sys.argv[2]) if len(sys.argv) > 2 else 60
iters = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
while True:
    r = tabu_indep(C, verts, s, iters, rng)
    print('s', s, 'found' if r else 'fail', round(time.time() - t0, 1), flush=True)
    if r is None: break
    best = r; s += 1
print('best partial ovoid size', len(best), 'time', round(time.time() - t0, 1))
np.save('/home/user/degree-diameter/research/squads/conics2-r1/c1/ovoid_best.npy', np.array(best))
