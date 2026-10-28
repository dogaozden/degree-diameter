"""Independent check (incidence only, not the quotient or edge files): a point set is valid when no line of H(7)
contains two of its points. Reads H(7) from the hexagon file and the point ids from a file."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q7.bin')
pts = [int(x) for x in open(sys.argv[1]).read().split()]
assert len(set(pts)) == len(pts), 'repeated points'
assert all(0 <= p < H.N for p in pts)
inS = np.zeros(H.N, dtype=bool)
inS[pts] = True
cnt = inS[H.lines].sum(axis=1)          # points of the set on each line
bad = int((cnt >= 2).sum())
print('points', len(pts), 'lines with >=2 set points', bad, 'VALID' if bad == 0 else 'INVALID')
