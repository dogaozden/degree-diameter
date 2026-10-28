"""Independent certificate for the set of points written by expand.py (does not use the quotient or expand code).
Checks: (1) the hexagon file really gives totally singular lines of Q(6,13) with pairwise orthogonal points (so every
line is a line of H(13) and the incidence data is the one used), (2) the chosen ids are distinct and in range,
(3) no line of H(13) contains two chosen points, i.e. the chosen points are pairwise non-collinear.
usage: certify.py POINTS_TXT"""
import struct, sys, numpy as np

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q13.bin'
P = 13
with open(HEX, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
    X = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
assert q == P and N == 402234 and L == 402234
assert X.min() >= 0 and X.max() < P

def Q(x):  # x0x4 + x1x5 + x2x6 - x3^2
    return (x[:, 0] * x[:, 4] + x[:, 1] * x[:, 5] + x[:, 2] * x[:, 6] - x[:, 3] * x[:, 3]) % P

def b(x, y):  # polar form, x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3
    return (x[:, 0] * y[:, 4] + x[:, 4] * y[:, 0] + x[:, 1] * y[:, 5] + x[:, 5] * y[:, 1]
            + x[:, 2] * y[:, 6] + x[:, 6] * y[:, 2] - 2 * x[:, 3] * y[:, 3]) % P

# (1) every point of the file is on Q, and the points of each line are pairwise orthogonal
assert (Q(X) == 0).all(), 'a point is not on the quadric'
assert len(set(map(tuple, X[:1000].tolist()))) == 1000
assert len(np.unique(X, axis=0)) == N, 'points not distinct'
for i in range(q + 1):
    for j in range(i + 1, q + 1):
        assert (b(X[lines[:, i]], X[lines[:, j]]) == 0).all(), 'line not totally singular'
print('hexagon data ok: N=%d lines=%d, each line totally singular' % (N, L), flush=True)

# (2) chosen points
S = np.loadtxt(sys.argv[1], dtype=np.int64, ndmin=1)
assert S.min() >= 0 and S.max() < N, 'id out of range'
assert len(np.unique(S)) == len(S), 'repeated point'
inS = np.zeros(N, dtype=np.int64); inS[S] = 1
# (3) no line of H(13) holds two chosen points
per_line = inS[lines].sum(axis=1)
print('max chosen points on a line', int(per_line.max()), flush=True)
assert per_line.max() <= 1, 'two chosen points are collinear'
print('CERTIFIED: %d pairwise non-collinear points of H(13) (bound 28731)' % len(S), flush=True)
