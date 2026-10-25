# c8: quick look (under 20 s): orbit sizes and number of independent orbits for an order-37 isometry.
import sys, time
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c8')
import orth as O
from ord37 import order_of, mpow
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = np.random.default_rng(seed)
found = []
for t in range(4000):
    k = int(rng.integers(3, 11))
    g = O.rand_elem(rng, k)
    o = order_of(g)
    if o is not None and o % 37 == 0:
        found.append((o, mpow(g, o // 37)))
        break
o, h = found[0]
print("sampled order", o, "-> element of order 37")
t0 = time.time()
cyc = O.cycles(O.perm_of(h))
lens = {}
for c in cyc: lens[len(c)] = lens.get(len(c), 0) + 1
print("orbit sizes", lens, round(time.time() - t0, 1), "s", flush=True)
ind = O.indep_orbits(cyc)
print("independent orbits:", len(ind))
np.save(f'/home/user/degree-diameter/research/squads/d14D7-r4/c8/h37_seed{seed}.npy', h)
