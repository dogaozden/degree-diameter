"""Build the two MIS graphs for H(7): lines adjacent when they meet; points adjacent when collinear."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

OUT = '/home/user/degree-diameter/research/squads/polylev/r1/c11/'
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q7.bin')
q, N, L = H.q, H.N, H.L
print('q', q, 'points', N, 'lines', L, 'pts per line', H.lines.shape[1], 'lines per point', H.PL.shape[1])
assert H.lines.shape == (L, q + 1) and H.PL.shape == (N, q + 1)


def write_graph(name, n, U, V):
    U = np.concatenate(U)
    V = np.concatenate(V)
    # sanity: no loops, no duplicate pairs
    assert (U != V).all()
    a = np.minimum(U, V)
    b = np.maximum(U, V)
    key = a * n + b
    assert len(np.unique(key)) == len(key), 'duplicate edges'
    m = len(key)
    with open(OUT + name, 'w') as f:
        f.write(f'{n} {m}\n')
        f.write('\n'.join(f'{x} {y}' for x, y in zip(a.tolist(), b.tolist())))
        f.write('\n')
    deg = np.bincount(np.concatenate([a, b]), minlength=n)
    print(name, 'n', n, 'm', m, 'deg min/max', deg.min(), deg.max())


# (a) lines: two lines adjacent when they share a point (every pair of lines through a point)
LU, LV = [], []
for i in range(q + 1):
    for j in range(i + 1, q + 1):
        LU.append(H.PL[:, i])
        LV.append(H.PL[:, j])
write_graph('lines_meet.txt', L, LU, LV)

# (b) points: two points adjacent when collinear (every pair of points on a line)
PU, PV = [], []
for i in range(q + 1):
    for j in range(i + 1, q + 1):
        PU.append(H.lines[:, i])
        PV.append(H.lines[:, j])
write_graph('points_collinear.txt', N, PU, PV)
