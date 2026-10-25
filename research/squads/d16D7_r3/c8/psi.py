#!/usr/bin/env python3
"""psi.py (card c8, squad d16D7 round 3): the wildcard collineation psi(v,a,w) = (A w, -a, A^-T v) of H(13).

g = (v,a,w) -> (M v, a, M^-T w) is the order-61 collineation (M = [[5,2,0],[12,5,2],[12,0,5]] mod 13).
A is chosen in SL(3,13) with A M^-T A^-1 = M^k, which gives psi g psi^-1 = g^k (psi normalises <g>).
psi = (alpha_A) o tau with alpha_A(v,a,w) = (A v, a, A^-T w) and tau(v,a,w) = (w,-a,v).

Writes psi_pts.bin and psi_lines.bin (int32 element permutations of the hex_q13 point / line ids) into this folder.
usage: psi.py
"""
import itertools
import sys

import numpy as np

P = 13
DATA = '/home/user/degree-diameter/research/squads/d16D7_r2/data/'
OUT = '/home/user/degree-diameter/research/squads/d16D7_r3/c8/'
INV = np.array([0] + [pow(a, P - 2, P) for a in range(1, P)], dtype=np.int64)
POW = P ** np.arange(7, dtype=np.int64)


def load_hex(fn):
    b = open(fn, 'rb').read()
    q, N, L = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
    LP = np.frombuffer(b[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
    X = np.frombuffer(b[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    assert len(X) == N and len(b) == 12 + 4 * L * (q + 1) + 7 * N
    return q, N, L, LP, X


def normalise(V):
    V = V % P
    lead = np.argmax(V != 0, axis=1)
    s = INV[V[np.arange(len(V)), lead]]
    return (V * s[:, None]) % P


class Index:
    def __init__(self, X):
        code = X @ POW
        self.order = np.argsort(code)
        self.sc = code[self.order]
        assert np.all(np.diff(self.sc) > 0), 'point codes not unique'

    def find(self, Y):
        yc = Y @ POW
        pos = np.minimum(np.searchsorted(self.sc, yc), len(self.sc) - 1)
        return self.order[pos], self.sc[pos] == yc


def inv_mod(A):
    n = A.shape[0]
    Mx = np.concatenate([A % P, np.eye(n, dtype=np.int64)], axis=1)
    for c in range(n):
        r = next(i for i in range(c, n) if Mx[i, c] % P)
        Mx[[c, r]] = Mx[[r, c]]
        Mx[c] = (Mx[c] * pow(int(Mx[c, c]), P - 2, P)) % P
        for i in range(n):
            if i != c and Mx[i, c]:
                Mx[i] = (Mx[i] - Mx[i, c] * Mx[c]) % P
    return Mx[:, n:]


def det_mod(a):
    d = (a[0, 0] * (a[1, 1] * a[2, 2] - a[1, 2] * a[2, 1])
         - a[0, 1] * (a[1, 0] * a[2, 2] - a[1, 2] * a[2, 0])
         + a[0, 2] * (a[1, 0] * a[2, 1] - a[1, 1] * a[2, 0]))
    return int(d) % P


def mpow(A, e):
    R = np.eye(A.shape[0], dtype=np.int64)
    B = A % P
    while e:
        if e & 1:
            R = (R @ B) % P
        B = (B @ B) % P
        e >>= 1
    return R


def nullspace_mod(Amat):
    A = Amat.copy() % P
    m, n = A.shape
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i, c] % P), None)
        if p is None:
            continue
        A[[r, p]] = A[[p, r]]
        A[r] = (A[r] * pow(int(A[r, c]), P - 2, P)) % P
        for i in range(m):
            if i != r and A[i, c]:
                A[i] = (A[i] - A[i, c] * A[r]) % P
        piv.append(c)
        r += 1
        if r == m:
            break
    basis = []
    for f in [c for c in range(n) if c not in piv]:
        v = np.zeros(n, dtype=np.int64)
        v[f] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-A[i, f]) % P
        basis.append(v)
    return basis


def main():
    q, N, L, LP, X = load_hex(DATA + 'hex_q13.bin')
    assert q == P
    assert np.array_equal(normalise(X), X), 'stored coordinates are not normalised (first nonzero = 1)'
    idx = Index(X)
    M = np.array([[5, 2, 0], [12, 5, 2], [12, 0, 5]], dtype=np.int64)
    Minv = inv_mod(M)
    I3 = np.eye(3, dtype=np.int64)
    order_M = next(e for e in range(1, 5000) if np.array_equal(mpow(M, e), I3))
    print('det M =', det_mod(M), ' order of M mod 13 =', order_M)

    gp = np.fromfile(DATA + 'g13o61_pts.bin', dtype=np.int32).astype(np.int64)
    gl = np.fromfile(DATA + 'g13o61_lines.bin', dtype=np.int32).astype(np.int64)
    Y = np.zeros_like(X)
    Y[:, 0:3] = (X[:, 0:3] @ M.T) % P
    Y[:, 3] = X[:, 3]
    Y[:, 4:7] = (X[:, 4:7] @ Minv) % P
    print('g = (Mv, a, M^-T w) matches the data on points:', np.array_equal(normalise(Y), X[gp]))

    # R: random 64-bit weights; a line is identified by the sum of the weights of its points (checked exactly later)
    rng = np.random.default_rng(12345)
    R = rng.integers(1, 2 ** 62, size=N, dtype=np.int64).astype(np.uint64)
    lh = R[LP].sum(axis=1)
    order_l = np.argsort(lh)
    sl = lh[order_l]
    assert len(np.unique(sl)) == L

    def line_perm_of(pts_perm):
        img = pts_perm[LP]
        ih = R[img].sum(axis=1)
        pos = np.minimum(np.searchsorted(sl, ih), L - 1)
        assert np.all(sl[pos] == ih), 'some image of a line is not a line'
        lp = order_l[pos]
        assert np.array_equal(np.sort(img, axis=1), np.sort(LP[lp], axis=1)), 'hash clash'
        assert len(np.unique(lp)) == L, 'not a bijection on lines'
        return lp

    # tau is a collineation (sanity check of the model)
    tau_Y = np.concatenate([X[:, 4:7], (-X[:, 3:4]) % P, X[:, 0:3]], axis=1)
    tau_pts, ok = idx.find(normalise(tau_Y))
    assert ok.all()
    line_perm_of(tau_pts)
    print('tau (v,a,w)->(w,-a,v) maps lines to lines: True')

    # order of g on points: 61 expected
    order_M_g = 0
    cur = np.arange(N)
    for j in range(1, 500):
        cur = gp[cur]
        if np.array_equal(cur, np.arange(N)):
            order_M_g = j
            break
    print('order of g on points =', order_M_g)

    Mt_inv = Minv.T % P      # M^-T
    results = []
    for k in [-1, -13, -169]:
        C = mpow(M, k % order_M)            # M^k
        E = np.zeros((9, 9), dtype=np.int64)
        for i in range(3):
            for j in range(3):
                row = 3 * i + j
                for kk in range(3):
                    E[row, 3 * i + kk] += Mt_inv[kk, j]     # (A M^-T)_{ij}
                    E[row, 3 * kk + j] -= C[i, kk]          # (M^k A)_{ij}
        basis = nullspace_mod(E)
        print('k =', k, ': intertwiner space dimension', len(basis))
        if not basis:
            continue
        A = None
        for coeffs in itertools.product(range(P), repeat=len(basis)):
            if not any(coeffs):
                continue
            x = sum(c * b for c, b in zip(coeffs, basis)) % P
            cand = x.reshape(3, 3)
            if det_mod(cand) == 1:
                A = cand
                break
        if A is None:
            print('   no det-1 intertwiner')
            continue
        assert np.array_equal((A @ Mt_inv) % P, (C @ A) % P)
        Ainv = inv_mod(A)
        # psi(v,a,w) = (A w, -a, A^-T v); row form: v' = w A^T, a' = -a, w' = v A^-1
        psiY = np.zeros_like(X)
        psiY[:, 0:3] = (X[:, 4:7] @ A.T) % P
        psiY[:, 3] = (-X[:, 3]) % P
        psiY[:, 4:7] = (X[:, 0:3] @ Ainv) % P
        psi_pts, ok = idx.find(normalise(psiY))
        assert ok.all() and len(np.unique(psi_pts)) == N, 'psi is not a permutation of the points'
        psi_lines = line_perm_of(psi_pts)
        # normalises <g>: psi g = g^j psi
        j_found = None
        cur = np.arange(N)
        cl = np.arange(L)
        for j in range(order_M_g):
            if np.array_equal(psi_pts[gp], cur[psi_pts]) and np.array_equal(psi_lines[gl], cl[psi_lines]):
                j_found = j
                break
            cur = gp[cur]
            cl = gl[cl]
        print('   det A = 1, A =', A.tolist())
        print('   psi is a collineation (points and lines); psi g psi^-1 = g^%s' % j_found)
        print('   psi maps points to points: yes (%d points)' % N)
        if j_found is None:
            continue
        results.append((k, A, psi_pts, psi_lines, j_found))
        break

    assert results, 'no psi found'
    k, A, psi_pts, psi_lines, j_found = results[0]
    np.asarray(psi_pts, dtype=np.int32).tofile(OUT + 'psi_pts.bin')
    np.asarray(psi_lines, dtype=np.int32).tofile(OUT + 'psi_lines.bin')
    with open(OUT + 'psi_info.txt', 'w') as f:
        f.write('k=%d A=%s psi g psi^-1 = g^%d\n' % (k, A.tolist(), j_found))
    print('wrote', OUT + 'psi_pts.bin', OUT + 'psi_lines.bin', ' with k =', k, 'j =', j_found)


if __name__ == '__main__':
    main()
