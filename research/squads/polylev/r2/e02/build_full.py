"""Build the collinearity graph of H(11) (points) as CSR: e02/pts11_{n,off,nb}.bin. Degree q(q+1)=132.
Two points are collinear iff they share a line of H(11); the neighbour set of x is the union of the other
points of the 12 lines through x (distinct, since H(q) has no two points on two lines)."""
import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
t0 = time.time()
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q11.bin')
N, q = H.N, H.q
D = q * (q + 1)
M = H.lines[H.PL].reshape(N, -1)                  # N x (q+1)^2: points on lines through x (x repeated q+1 times)
mask = M != np.arange(N)[:, None]
A = M[mask].reshape(N, D).astype(np.int32)
A.sort(axis=1)
assert (np.diff(A, axis=1) > 0).all(), 'neighbour lists not distinct'
print('N', N, 'D', D, 'built', round(time.time() - t0, 1), 's', flush=True)
out = '/home/user/degree-diameter/research/squads/polylev/r2/e02/'
np.array([N], dtype=np.int32).tofile(out + 'pts11_n.bin')
np.arange(0, N * D + 1, D, dtype=np.int32).tofile(out + 'pts11_off.bin')
A.tofile(out + 'pts11_nb.bin')
print('wrote CSR', flush=True)
