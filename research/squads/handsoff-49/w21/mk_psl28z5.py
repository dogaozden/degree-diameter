# Build the table of PSL(2,8) x Z_5 (= SL(2,8) x Z_5, order 2520), identity = index 0.
# GF(8) = F_2[x]/(x^3+x+1). Elements are ints 0..7 (bit i = coefficient of x^i).
import sys
import numpy as np

POLY = 0b1011

def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= POLY
    return r

def mm(m1, m2):
    a, b, c, d = m1
    e, f, g, h = m2
    return (gmul(a, e) ^ gmul(b, g), gmul(a, f) ^ gmul(b, h),
            gmul(c, e) ^ gmul(d, g), gmul(c, f) ^ gmul(d, h))

# all 2x2 matrices over GF(8) with det 1 (det = ad + bc in characteristic 2)
mats = []
for a in range(8):
    for b in range(8):
        for c in range(8):
            for d in range(8):
                if gmul(a, d) ^ gmul(b, c) == 1:
                    mats.append((a, b, c, d))
assert len(mats) == 504, len(mats)
ident = (1, 0, 0, 1)
mats.remove(ident)
mats = [ident] + mats
idx = {m: i for i, m in enumerate(mats)}
M = len(mats)
TS = np.empty((M, M), dtype=np.int64)
for i, x in enumerate(mats):
    for j, y in enumerate(mats):
        TS[i, j] = idx[mm(x, y)]
# direct product with Z_5
K = 5
N = M * K
T = np.empty((N, N), dtype=np.uint16)
for i in range(M):
    for k in range(K):
        row = i * K + k
        cols = (TS[i][:, None] * K + (k + np.arange(K))[None, :] % K)  # shape (M, K)
        # index of (TS[i,j], (k+l)%K) for j in range(M), l in range(K)
        full = np.empty((M, K), dtype=np.int64)
        full[:, :] = TS[i][:, None] * K + ((k + np.arange(K)) % K)[None, :]
        T[row] = full.reshape(-1).astype(np.uint16)
assert N == 2520
# sanity: identity row/column, associativity on random triples
rng = np.random.default_rng(1)
for _ in range(20000):
    a, b, c = rng.integers(0, N, 3)
    assert T[T[a, b], c] == T[a, T[b, c]]
assert all(T[0, x] == x and T[x, 0] == x for x in range(N))
out = sys.argv[1]
with open(out, "wb") as f:
    np.array([N], dtype=np.int32).tofile(f)
    T.tofile(f)
print("wrote", out, "N", N)
