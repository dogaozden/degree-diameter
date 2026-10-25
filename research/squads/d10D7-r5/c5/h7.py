# c5 helpers: H(7) points, B form, S = 288-set; stabiliser search in PGO_7(7).
import numpy as np, struct
HEX7 = '/home/user/degree-diameter/research/d10D7/hex/hex_q7.bin'
def load_hex(path):
    with open(path, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12))
        lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype='<i4').reshape(L, q + 1).astype(np.int64)
        coords = np.frombuffer(f.read(7 * N), dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return q, N, lines, coords
def Bmat(X, Y, q):
    # X (a,7), Y (b,7) -> (a,b) polar form mod q (odd q): x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3
    return (X[:, [0, 4, 1, 5, 2, 6]] @ Y[:, [4, 0, 5, 1, 6, 2]].T - 2 * np.outer(X[:, 3], Y[:, 3])) % q
def qval(X, q):
    return (X[:, 0] * X[:, 4] + X[:, 1] * X[:, 5] + X[:, 2] * X[:, 6] - X[:, 3] ** 2) % q
def normalize(v, q):
    v = np.asarray(v) % q
    nz = np.nonzero(v)[0]
    if len(nz) == 0: return None
    inv = pow(int(v[nz[0]]), q - 2, q)
    return (v * inv) % q
