# For a flag set (point ids from E' + str(p) + '.map), count its points in every hyperplane of V = {x4 = -x0} (6-dim over F_11).
import sys, itertools
import numpy as np
p = int(sys.argv[2]) if len(sys.argv) > 2 else 11
rows = np.loadtxt('/home/user/degree-diameter/research/cell147/data/E' + str(p) + '.map', dtype=np.int64)
pos = {int(r[0]): i for i, r in enumerate(rows)}
fl = [int(l.split()[0]) for l in open(sys.argv[1])]
U = rows[[pos[a] for a in fl]][:, [2, 3, 4, 5, 7, 8]] % p          # (x0,x1,x2,x3,x5,x6)
# all normalized normals (first nonzero = 1)
allv = np.array(list(itertools.product(range(p), repeat=6)), dtype=np.int64)
nz = allv[np.any(allv != 0, axis=1)]
first = np.argmax(nz != 0, axis=1)
nrm = nz[nz[np.arange(len(nz)), first] == 1]
cnt = ((nrm @ U.T) % p == 0).sum(axis=1)
h = np.bincount(cnt)
print("points", len(fl), "hyperplane count histogram (count: #hyperplanes) top:", [(c, int(h[c])) for c in range(len(h)) if h[c] and c >= 10])
