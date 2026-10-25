# analyse.py SETFILE: how the points of an H(8) set sit on the GF(64)-lines (= PG(2,64) points) of PG(5,8)
import sys, struct, collections, numpy as np
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
MUL8 = np.zeros((8, 8), dtype=np.int64)
for x in range(8):
    for y in range(8):
        a = [(x >> i) & 1 for i in range(3)]; b = [(y >> i) & 1 for i in range(3)]
        r = [0] * 5
        for i in range(3):
            for j in range(3): r[i + j] ^= a[i] & b[j]
        for k in (4, 3):
            if r[k]: r[k] = 0; r[k - 3] ^= 1; r[k - 2] ^= 1
        MUL8[x, y] = r[0] | (r[1] << 1) | (r[2] << 2)
INV8 = {x: y for x in range(1, 8) for y in range(1, 8) if MUL8[x, y] == 1}
raw = open(HEX, 'rb').read(); N = struct.unpack('<iii', raw[:12])[1]
X = np.frombuffer(raw[12 + N * 36:12 + N * 36 + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64)
S = [int(x) for x in open(sys.argv[1]).read().split()]
def m64(p, q, r, s): return (MUL8[p, r] ^ MUL8[q, s], MUL8[p, s] ^ MUL8[q, r] ^ MUL8[q, s])
def pt64(v):  # v: list of 3 GF(64) elements (pairs) -> normalised tuple
    f = next(e for e in v if e != (0, 0)); p, q = f
    # inverse of f in GF(64): brute force
    for r in range(8):
        for s in range(8):
            if m64(p, q, r, s) == (1, 0): inv = (r, s)
    return tuple(m64(inv[0], inv[1], a, b) for (a, b) in v)
lines = collections.Counter(); curve = 0
for idx in S:
    x = X[idx]
    v = [(int(x[0]), int(x[4])), (int(x[1]), int(x[5])), (int(x[2]), int(x[6]))]
    nrm = 0
    for (a, b) in v: nrm ^= int(MUL8[a, a] ^ MUL8[a, b] ^ MUL8[b, b])
    key = pt64(v); lines[key] += 1
    if nrm == 0: curve += 1
print('points', len(S), 'GF(64)-lines used', len(lines), 'points on curve lines', curve)
print('points per GF(64)-line histogram:', sorted(collections.Counter(lines.values()).items()))
