"""Independent check of a point set for H(8): pairwise non-collinear (no line of H(8) holds two of them).
usage: verify_points.py HEXBIN SETFILE   (SETFILE: one point id per line). Prints K and VALID; exit 1 if invalid."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
H = Hex(sys.argv[1])
S = sorted(set(int(x) for x in open(sys.argv[2]).read().split()))
assert all(0 <= p < H.N for p in S)
cnt = np.zeros(H.L, dtype=np.int64)
for p in S:
    cnt[H.PL[p]] += 1
ok = bool((cnt <= 1).all())
print('K', len(S), 'VALID' if ok else 'INVALID', 'pairwise non-collinear' if ok else '')
sys.exit(0 if ok else 1)
