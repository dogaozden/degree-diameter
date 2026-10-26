# Matrix groups PSL(2,q) / PGL(2,q) for prime q as index-based groups: identity = index 0,
# mul(x_idx, y_idx) vectorised via canonical codes and searchsorted.
import numpy as np

def make_group(kind, q):
    inv = np.zeros(q, dtype=np.int64)
    for x in range(1, q):
        inv[x] = pow(x, q - 2, q)
    def canon(a, b, c, d):
        if kind == 'PGL':
            lead = np.where(a != 0, a, np.where(b != 0, b, np.where(c != 0, c, d)))
            iv = inv[lead]
            a, b, c, d = a * iv % q, b * iv % q, c * iv % q, d * iv % q
            return ((a * q + b) * q + c) * q + d
        # PSL: min of M and -M
        c1 = ((a * q + b) * q + c) * q + d
        na, nb, nc, nd = (q - a) % q, (q - b) % q, (q - c) % q, (q - d) % q
        c2 = ((na * q + nb) * q + nc) * q + nd
        return np.minimum(c1, c2)
    rng = np.arange(q, dtype=np.int64)
    A, B, C, D = np.meshgrid(rng, rng, rng, rng, indexing='ij')
    A, B, C, D = A.ravel(), B.ravel(), C.ravel(), D.ravel()
    det = (A * D - B * C) % q
    if kind == 'PGL':
        sel = det != 0
    else:
        sel = det == 1
    A, B, C, D = A[sel], B[sel], C[sel], D[sel]
    codes = np.unique(canon(A, B, C, D))
    I = canon(np.array([1]), np.array([0]), np.array([0]), np.array([1]))[0]
    i0 = int(np.searchsorted(codes, I))
    assert codes[i0] == I
    codes = np.concatenate([[I], np.delete(codes, i0)])
    # sorted tail for searchsorted
    head = codes[0]; tail = np.sort(codes[1:])
    E = np.concatenate([[head], tail])  # index 0 = identity; E[1:] sorted
    order = np.argsort(E[1:]) + 1
    sortedkeys = E[1:][np.argsort(E[1:])]
    sortidx = np.argsort(E[1:]) + 1  # map sorted position -> element index
    N = len(E)
    def decode(x):
        c = E[x]
        d = c % q; c = c // q
        cc = c % q; c = c // q
        b = c % q; a = c // q
        return a, b, cc, d
    def mul(x, y):
        x = np.asarray(x, dtype=np.int64); y = np.asarray(y, dtype=np.int64)
        x, y = np.broadcast_arrays(x, y)
        a1, b1, c1, d1 = decode(x)
        a2, b2, c2, d2 = decode(y)
        A = (a1 * a2 + b1 * c2) % q
        B = (a1 * b2 + b1 * d2) % q
        C = (c1 * a2 + d1 * c2) % q
        Dd = (c1 * b2 + d1 * d2) % q
        cd = canon(A, B, C, Dd)
        pos = np.searchsorted(sortedkeys, cd)
        pos = np.minimum(pos, len(sortedkeys) - 1)
        out = sortidx[pos]
        out = np.where(cd == I, 0, out)
        assert np.all(E[out] == cd), "product left the group"
        return out
    return N, mul
