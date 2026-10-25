import os, sys, numpy as np
from geo import Geo, sl3, orbits
q = int(sys.argv[1])
H = Geo(f'/tmp/bcdt/hex/hex_q{q}.bin')
N = H.N
gens = []
for (i, j) in [(0, 1), (1, 2), (2, 0), (1, 0), (2, 1), (0, 2)]:
    g = np.eye(3, dtype=np.int64); g[i, j] = 1
    gens.append(H.act(sl3(g, q)))
po = orbits([g[0] for g in gens], N)
lo = orbits([g[1] for g in gens], N)
print('q', q, 'N', N)
print('point orbit sizes', np.bincount(po))
print('line orbit sizes', np.bincount(lo))
# flags
fl = [(p, l) for p in range(N) for l in H.plines[p]]
fid = {f: i for i, f in enumerate(fl)}
fperms = [np.array([fid[(gp[p], gl[l])] for (p, l) in fl]) for gp, gl in gens]
fo = orbits(fperms, len(fl))
print('flag orbits', len(np.unique(fo)), np.bincount(fo))
for o in range(len(np.unique(fo))):
    i = int(np.where(fo == o)[0][0]); p, l = fl[i]
    print('  flag orbit', o, 'point orbit', po[p], 'line orbit', lo[l], 'size', np.sum(fo == o))
np.savez(os.environ.get('SCRATCH', '/tmp') + f'/sl3_q{q}.npz', po=po, lo=lo,
         gp=np.array([g[0] for g in gens]), gl=np.array([g[1] for g in gens]))
