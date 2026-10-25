# c5: GF(8) with x^3 = x+1 (element a0+2a1+4a2), hex_q8 coordinates, H(8) point model via projection from nucleus.
import numpy as np, struct
MUL = np.zeros((8, 8), dtype=np.int64)
def hm(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
for a in range(8):
    for b in range(8): MUL[a, b] = hm(a, b)
INV = np.zeros(8, dtype=np.int64)
for a in range(1, 8):
    for b in range(1, 8):
        if MUL[a, b] == 1: INV[a] = b
SQ4 = np.array([MUL[MUL[a, a], MUL[a, a]] for a in range(8)])  # a^4 = sqrt(a) in GF(8)
def load_hex8(path='/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'):
    with open(path, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12))
        f.seek(12 + 4 * L * (q + 1))
        X = np.frombuffer(f.read(7 * N), dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return q, N, X
def gf_matvec(T, V):
    """T: (r,c) over GF(2) (0/1), V: (m,c) GF(8) vectors -> (m,r) GF(8): XOR of selected columns."""
    m, c = V.shape; r = T.shape[0]
    out = np.zeros((m, r), dtype=np.int64)
    for i in range(r):
        acc = np.zeros(m, dtype=np.int64)
        for j in range(c):
            if T[i, j]: acc ^= V[:, j]
        out[:, i] = acc
    return out
def normalize_rows(V):
    nz = V != 0
    first = np.argmax(nz, axis=1)
    lead = V[np.arange(V.shape[0]), first]
    return MUL[INV[lead][:, None], V]
