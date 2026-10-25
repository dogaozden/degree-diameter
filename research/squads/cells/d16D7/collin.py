#!/usr/bin/env python3
"""collin.py: a collineation of H(q) (hexgen model) from SL(3,q) acting as (v, a, w) -> (g v, a, g^-T w), with
v = (x0,x1,x2), a = x3, w = (x4,x5,x6) (it preserves X0X4 + X1X5 + X2X6 - X3^2). Checks that it maps every line of
hex_q{q}.bin onto a line, and writes the point and line permutations.
usage: collin.py HEXBIN ORDER OUTPREFIX     (q prime; g = power of a Singer cycle of GL(3,q) of the given order)
writes OUTPREFIX_pts.npy/.bin, OUTPREFIX_lines.npy/.bin (int32 permutations; .bin raw) and prints orbit statistics."""
import sys
import numpy as np


def load(fn):
    b = open(fn, 'rb').read()
    q, N, L = np.frombuffer(b[:12], dtype=np.int32)
    LP = np.frombuffer(b[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1)
    X = np.frombuffer(b[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return int(q), int(N), LP, X


def matmul(A, B, q):
    return (A @ B) % q


def matpow(A, e, q):
    R = np.eye(3, dtype=np.int64)
    while e:
        if e & 1:
            R = matmul(R, A, q)
        A = matmul(A, A, q)
        e >>= 1
    return R


def matinv(A, q):
    M = np.concatenate([A % q, np.eye(3, dtype=np.int64)], axis=1)
    for c in range(3):
        r = next(i for i in range(c, 3) if M[i, c] % q)
        M[[c, r]] = M[[r, c]]
        M[c] = (M[c] * pow(int(M[c, c]), q - 2, q)) % q
        for i in range(3):
            if i != c and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[c]) % q
    return M[:, 3:]


def singer(q):
    """companion matrix of a primitive cubic over F_q (order q^3 - 1)"""
    n = q ** 3 - 1
    fac = [p for p in range(2, n + 1) if n % p == 0 and all(p % d for d in range(2, int(p ** 0.5) + 1))]
    for c0 in range(1, q):
        for c1 in range(q):
            for c2 in range(q):
                C = np.array([[0, 0, (-c0) % q], [1, 0, (-c1) % q], [0, 1, (-c2) % q]], dtype=np.int64)
                if not np.array_equal(matpow(C, n, q), np.eye(3, dtype=np.int64)):
                    continue
                if all(not np.array_equal(matpow(C, n // p, q), np.eye(3, dtype=np.int64)) for p in fac):
                    return C
    raise RuntimeError('no primitive cubic')


def normalise(V, q):
    V = V % q
    lead = np.argmax(V != 0, axis=1)
    inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
    s = inv[V[np.arange(len(V)), lead]]
    return (V * s[:, None]) % q


def main():
    hexfn, order, outp = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    q, N, LP, X = load(hexfn)
    C = singer(q)
    n = q ** 3 - 1
    assert n % order == 0
    g = matpow(C, n // order, q)
    assert np.array_equal(matpow(g, order, q), np.eye(3, dtype=np.int64))
    det = int(round(np.linalg.det(g))) % q
    print('g =', g.tolist(), 'det', det)
    gi_t = matinv(g, q).T % q
    code = X @ (q ** np.arange(7))
    order_idx = np.argsort(code)
    sc = code[order_idx]
    Y = np.zeros_like(X)
    Y[:, 0:3] = (X[:, 0:3] @ g.T) % q
    Y[:, 3] = X[:, 3]
    Y[:, 4:7] = (X[:, 4:7] @ gi_t.T) % q
    Y = normalise(Y, q)
    yc = Y @ (q ** np.arange(7))
    pos = np.searchsorted(sc, yc)
    assert np.all(sc[pos] == yc), 'image not a point of the quadric'
    perm_p = order_idx[pos].astype(np.int32)
    assert len(np.unique(perm_p)) == N
    # lines: map point sets, look up sorted tuples
    key = np.sort(LP, axis=1)
    img = np.sort(perm_p[LP], axis=1)
    kv = {tuple(r): i for i, r in enumerate(map(tuple, key))}
    perm_l = np.empty(len(LP), dtype=np.int32)
    bad = 0
    for i, r in enumerate(map(tuple, img)):
        j = kv.get(r)
        if j is None:
            bad += 1
            perm_l[i] = -1
        else:
            perm_l[i] = j
    print('lines not mapped to lines:', bad)
    if bad:
        sys.exit(1)
    for name, pm in (('points', perm_p), ('lines', perm_l)):
        seen = np.zeros(len(pm), bool)
        sizes = {}
        for s in range(len(pm)):
            if seen[s]:
                continue
            c = 0
            x = s
            while not seen[x]:
                seen[x] = True
                x = pm[x]
                c += 1
            sizes[c] = sizes.get(c, 0) + 1
        print(name, 'orbit sizes:', sizes)
    np.save(outp + '_pts.npy', perm_p)
    np.save(outp + '_lines.npy', perm_l)
    perm_p.astype(np.int32).tofile(outp + '_pts.bin')
    perm_l.astype(np.int32).tofile(outp + '_lines.bin')


if __name__ == '__main__':
    main()
