import sys, numpy as np, itertools
sys.path.insert(0, '../tools'); import hexlib
from f9 import *
q, lines, coord = hexlib.load('../hex/hex_q9.bin'); P = coord.astype(np.int64); N = len(P)
pairs = list(itertools.combinations(range(7), 2))
Wb = np.load('Wbasis.npy'); rad = np.load('Wrad.npy'); G21 = np.load('G21.npy')
_, pivW = rref(Wb.copy())
Pi = nullspace(rad)          # rows: functionals on the 14 coefficient coordinates vanishing on the radical
assert Pi.shape == (7, 14)
# Plucker vectors of all lines, vectorised
x = P[lines[:, 0]]; y = P[lines[:, 1]]
PLK = np.stack([A[M[x[:, i], y[:, j]], NEG[M[x[:, j], y[:, i]]]] for i, j in pairs], 1)
C = PLK[:, pivW]             # coefficients w.r.t. the RREF basis of W
# sanity: reconstruct
img = np.zeros((N, 7), np.int64)
for r in range(7):
    s = np.zeros(N, np.int64)
    for c in range(14): s = A[s, M[Pi[r, c], C[:, c]]]
    img[:, r] = s
nz = (img != 0).any(1); print('all images nonzero:', nz.all())
first = np.argmax(img != 0, axis=1); lead = img[np.arange(N), first]
imgn = M[INV[lead][:, None], img]
codes = imgn @ (9 ** np.arange(7))
print('distinct image points:', len(np.unique(codes)), 'of', N)
# pencils: lines through each point
pl = hexlib.point_lines(lines, N)
bad = 0
for p in range(0, N, 97):
    R, _ = rref(imgn[pl[p]].copy())
    if len(R) != 2: bad += 1
print('pencils not on a projective line (sampled):', bad)
np.save('line_image.npy', imgn); np.save('Pi.npy', Pi)
# induced form on W/I: compute Gram of B_W on the images of a few basis lifts
