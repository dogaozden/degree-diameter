"""Independent certificate for a set of points of H(16) (e06).

usage: python3 -I verify_q16.py HEX_BIN SET_TXT
SET_TXT: first line = count, then one point id per line.

Checks (none of this uses the search code):
  1. the hexagon file has N points, N lines, every point on 17 lines, every line 17 distinct points;
  2. every point is singular: x0x4 + x1x5 + x2x6 + x3^2 = 0 over GF(16) (char 2);
  3. every line is totally singular: its points are pairwise orthogonal (b = 0);
  4. the chosen ids are distinct, in range, and the stated count matches;
  5. no line of H(16) contains two chosen points (non-collinearity).
GF(16) = GF(2)[x]/(x^4+x+1); addition is XOR; the coordinates use this encoding (as in hexlib.py).
"""
import sys
import numpy as np

hexpath, setpath = sys.argv[1], sys.argv[2]

# GF(16) multiplication table, built from the polynomial x^4 + x + 1 (0b10011)
def gmul(a, b):
    r = 0
    for bit in range(4):
        if (b >> bit) & 1:
            r ^= a << bit
    for k in (7, 6, 5, 4):
        if (r >> k) & 1:
            r ^= 0b10011 << (k - 4)
    return r

MUL = np.array([[gmul(a, b) for b in range(16)] for a in range(16)], dtype=np.uint8)

with open(hexpath, 'rb') as f:
    q, N, L = (int(v) for v in np.frombuffer(f.read(12), dtype=np.int32))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
    coord = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7)
assert q == 16 and N == 1118481 and L == N, (q, N, L)
ok = True

# 1. structure
deg = np.bincount(lines.ravel(), minlength=N)
print('points on 17 lines each:', bool((deg == q + 1).all()))
srt = np.sort(lines, axis=1)
distinct = bool((np.diff(srt, axis=1) != 0).all())
print('17 distinct points per line:', distinct)
ok &= bool((deg == q + 1).all()) and distinct

# 2. singular points
x = coord
Qv = MUL[x[:, 0], x[:, 4]] ^ MUL[x[:, 1], x[:, 5]] ^ MUL[x[:, 2], x[:, 6]] ^ MUL[x[:, 3], x[:, 3]]
print('all points singular:', bool((Qv == 0).all()))
ok &= bool((Qv == 0).all())

# 3. lines totally singular (pairwise orthogonal), chunked
I, J = np.triu_indices(q + 1, 1)
bad_lines = 0
CH = 40000
for s in range(0, L, CH):
    P = coord[lines[s:s + CH]]              # (c, 17, 7)
    X = P[:, I, :]
    Y = P[:, J, :]
    b = (MUL[X[..., 0], Y[..., 4]] ^ MUL[X[..., 4], Y[..., 0]] ^
         MUL[X[..., 1], Y[..., 5]] ^ MUL[X[..., 5], Y[..., 1]] ^
         MUL[X[..., 2], Y[..., 6]] ^ MUL[X[..., 6], Y[..., 2]])
    bad_lines += int((b != 0).any(axis=1).sum())
print('lines with a non-orthogonal pair:', bad_lines)
ok &= bad_lines == 0

# 4. the set
with open(setpath) as f:
    toks = f.read().split()
cnt = int(toks[0])
ids = np.array([int(t) for t in toks[1:]], dtype=np.int64)
print('stated count:', cnt, 'listed:', len(ids))
ok &= cnt == len(ids)
ok &= bool(((ids >= 0) & (ids < N)).all())
ok &= len(np.unique(ids)) == len(ids)

# 5. non-collinearity: every line carries at most one chosen point
mask = np.zeros(N, dtype=np.int64)
mask[ids] = 1
per_line = mask[lines].sum(axis=1)
maxline = int(per_line.max()) if L else 0
print('max chosen points on one line:', maxline)
ok &= maxline <= 1

print('K =', len(ids), 'valid =', bool(ok))
