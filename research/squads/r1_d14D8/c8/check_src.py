"""check_src.py: independent numpy check of walk reach sets (exact length D-1) for one or more A-sources.
python3 check_src.py BASEFILE D src1,src2,...   prints uncovered (B-vertex, level) counts."""
import sys
import numpy as np

fn, D, srcs = sys.argv[1], int(sys.argv[2]), [int(x) for x in sys.argv[3].split(',')]
with open(fn) as f:
    nA, nB, m = (int(x) for x in f.readline().split())
    E = np.loadtxt(f, dtype=np.int64, ndmin=2)
a, b, v = E[:, 0], E[:, 1], E[:, 2] % m
for s in srcs:
    # state: A-side reach (nA x m) and B-side reach (nB x m) as boolean arrays
    RA = np.zeros((nA, m), dtype=bool); RB = np.zeros((nB, m), dtype=bool)
    RA[s, 0] = True
    side = 0
    for step in range(D - 1):
        if side == 0:
            NB = np.zeros((nB, m), dtype=bool)
            # (a,g) -> (b, g+v)
            for e in range(len(a)):
                NB[b[e]] |= np.roll(RA[a[e]], v[e])
            RB = NB; side = 1
        else:
            NA = np.zeros((nA, m), dtype=bool)
            for e in range(len(a)):
                NA[a[e]] |= np.roll(RB[b[e]], -v[e])
            RA = NA; side = 0
    unc = int((~RB).sum()) if (D - 1) % 2 == 1 else int((~RB).sum())
    print(f'src {s}: uncovered B-pairs at exact length {D-1}: {unc}', flush=True)
