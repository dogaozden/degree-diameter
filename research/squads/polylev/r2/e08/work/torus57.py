"""Order-57 (= q^2-q+1, q=8) torus element of G2(8) acting semiregularly on the POINTS of H(8).
Reuses g2.py's collineation generators (random apartments); unlike g2.main it does not require the lines to be
semiregular (the line action has orbits of size 19 and 57 in the r1 search). Writes points permutation only.
usage: torus57.py HEXBIN OUT.pperm [SEED]"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
import numpy as np
from hexlib import Hex
import g2
hexbin, out = sys.argv[1], sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = np.random.default_rng(seed)
H = Hex(hexbin); H.bfs(0); q = H.q; k = q * q - q + 1
F = g2.F7(H)
gens = []
while len(gens) < 2:
    A = g2.random_apartment(H, rng); g = g2.apartment_map(H, A, rng)
    if g is not None: gens.append(g); print('collineation found', flush=True)
G2 = q ** 6 * (q ** 6 - 1) * (q ** 2 - 1); E = G2 * (q - 1)
for trial in range(400):
    w = rng.integers(0, 2, size=6)
    g = np.eye(7, dtype=np.int64)
    for b in w: g = F.mul(g, gens[b])
    g = F.mul(g, F.mul(gens[0], gens[1]))
    o = g2.proj_order(F, g, E)
    if o % k: continue
    h = F.pw(g, o // k)
    if g2.proj_order(F, h, k) != k: continue
    pm = H.point_ids(H.matvec(h, H.coord))
    seen = np.zeros(len(pm), dtype=bool); sizes = []
    for s in range(len(pm)):
        if seen[s]: continue
        x, c = s, 0
        while not seen[x]: seen[x] = True; x = pm[x]; c += 1
        sizes.append(c)
    print(f'trial {trial}: point orbits {len(sizes)} sizes {sorted(set(sizes))}', flush=True)
    if set(sizes) == {k}:
        np.savetxt(out + '.h', h, fmt='%d'); pm.astype(np.int32).tofile(out)
        print('written', out, flush=True); break
