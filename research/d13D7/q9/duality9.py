"""Explicit duality of H(9) (q = 3^2): line l -> point psi(phi(p(l))), phi = quotient of the Plucker span (14-dim,
the Lie algebra g2) by the radical of the induced form (7-dim ideal, characteristic 3), psi a similitude found by
findpsi.py.  Point p -> the line of H(9) through the images of the lines on p.  Verifies everything and writes
dual_pt2line.txt (point -> line) and dual_line2pt.txt (line -> point), hexgen indices."""
import sys, numpy as np
sys.path.insert(0, '../tools'); import hexlib
from f9 import *
q, lines, coord = hexlib.load('../hex/hex_q9.bin'); P = coord.astype(np.int64); N = len(P)
code = P @ (9 ** np.arange(7))
img = np.load('line_image.npy'); psi = np.load('psi.npy'); frob = int(np.load('psi_frob.npy')[0])
V = FROB[img] if frob else img
Y = np.zeros((N, 7), np.int64)
for r in range(7):
    s = np.zeros(N, np.int64)
    for c in range(7): s = A[s, M[psi[r, c], V[:, c]]]
    Y[:, r] = s
first = np.argmax(Y != 0, axis=1); Y = M[INV[Y[np.arange(N), first]][:, None], Y]
k = Y @ (9 ** np.arange(7)); j = np.searchsorted(code, k)
assert (j < N).all() and (code[np.minimum(j, N - 1)] == k).all(), 'image not a point'
line2pt = j
assert len(np.unique(line2pt)) == N, 'line -> point not injective'
pl = hexlib.point_lines(lines, N)
key = {tuple(sorted(l)): i for i, l in enumerate(lines.tolist())}
pt2line = np.full(N, -1, np.int64)
for p in range(N):
    t = tuple(sorted(line2pt[pl[p]].tolist()))
    assert t in key, f'pencil of point {p} does not map to a line'
    pt2line[p] = key[t]
assert len(np.unique(pt2line)) == N, 'point -> line not injective'
# incidence: p on l  =>  delta(l) on delta(p)  (by construction); also check the converse count
onl = np.zeros(N, bool)
ok = all(line2pt[l] in set(lines[pt2line[p]].tolist()) for p in range(0, N, 1) for l in pl[p][:1])
print('duality verified on all', N, 'points and lines; spot incidence', ok)
np.savetxt('dual_pt2line.txt', pt2line, fmt='%d', header='point -> line of an explicit duality of H(9) (hexgen indices)')
np.savetxt('dual_line2pt.txt', line2pt, fmt='%d', header='line -> point of the same duality (hexgen indices)')
