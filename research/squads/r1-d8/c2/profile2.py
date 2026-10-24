"""Profile unreached lift targets from source (x=0, g=0): classify by (H-distance from x, lift group element)."""
import collections, sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c2')
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh, holo
from unreached_profile import load_base, bfs

path, k = sys.argv[1], int(sys.argv[2])
srcs = [int(s) for s in sys.argv[3].split(',')]
H = gh.load(5)
N = H.N
NB, M1, M2, adj = load_base(path)
M = M1 * M2
for s in srcs:
    dH = holo.bfs(H, s)
    dist = bfs(NB, M1, M2, adj, s, 8)
    cnt = collections.Counter(); tot = 0
    for z in np.nonzero(dist == 255)[0]:
        y, g = divmod(int(z), M)
        g1, g2 = divmod(g, M2)
        tot += 1
        cnt[(dH[y], 'pt' if y < N else 'ln')] += 1
    per_kind = dict(sorted(cnt.items()))
    print(f'source {s} (point): unreached {tot}; by (H-dist, kind): {per_kind}', flush=True)
    # group-element distribution of unreached (per H-dist)
    gc = collections.Counter()
    for z in np.nonzero(dist == 255)[0]:
        y, g = divmod(int(z), M)
        if dH[y] == 6:
            gc[divmod(g, M2)] += 1
    print('   unreached at H-dist 6 by (Z5, Zk):', dict(sorted(gc.items())), flush=True)
