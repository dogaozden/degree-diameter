import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
import numpy as np
from hexlib import Hex
from spreadpart import find_singer, mat_pow
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q8.bin')
rng = np.random.default_rng(5)
g = find_singer(H, rng)
print('g=', g.tolist(), flush=True)
pm = H.sl3_point_map(g)
lm = H.line_map(pm)
def orbits(perm):
    n = len(perm); orb = -np.ones(n, dtype=np.int64); sizes = []
    c = 0
    for s in range(n):
        if orb[s] >= 0: continue
        x = s; k = 0
        while orb[x] < 0:
            orb[x] = c; x = perm[x]; k += 1
        sizes.append(k); c += 1
    return orb, sizes
po, ps = orbits(pm)
lo, ls = orbits(lm)
from collections import Counter
print('point orbits', len(ps), Counter(ps), flush=True)
print('line orbits', len(ls), Counter(ls), flush=True)
np.savetxt('S73.g', g, fmt='%d')
pm.astype(np.int32).tofile('S73.pperm'); lm.astype(np.int32).tofile('S73.lperm')
po.astype(np.int32).tofile('S73.porb'); lo.astype(np.int32).tofile('S73.lorb')
