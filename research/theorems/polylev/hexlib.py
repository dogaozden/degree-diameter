"""hexlib.py: the split Cayley hexagon H(q) as written by research/d10D7/hexgen2.c, with field arithmetic,
point lookup, the SL(3,q) action (v, a, w) -> (g v, a, g^{-T} w), and incidence helpers.

Coordinates: x = (x0..x6) on Q(x) = x0 x4 + x1 x5 + x2 x6 - x3^2, v = (x0, x1, x2), a = x3, w = (x4, x5, x6).
Field GF(p^e): element a0 + a1 p + ..., reduced mod the same irreducible polynomials as hexgen2.c.
"""
import struct
import numpy as np

POLY = {4: [1, 1], 8: [1, 1, 0], 9: [1, 0], 16: [1, 1, 0, 0], 25: [2, 0], 27: [1, 2, 0], 32: [1, 0, 1, 0, 0]}


def field(q):
    p = q
    for cand in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        if q % cand == 0:
            p = cand
            break
    e = 1
    while p ** e < q:
        e += 1
    c = POLY.get(q, [0] * e)

    def digits(x):
        d = []
        for _ in range(e):
            d.append(x % p)
            x //= p
        return d

    def undig(d):
        s, pw = 0, 1
        for a in d:
            s += (a % p) * pw
            pw *= p
        return s

    ADD = np.zeros((q, q), dtype=np.int64)
    MUL = np.zeros((q, q), dtype=np.int64)
    for x in range(q):
        for y in range(q):
            a, b = digits(x), digits(y)
            ADD[x, y] = undig([(a[i] + b[i]) % p for i in range(e)])
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if not f:
                    continue
                r[k] = 0
                for i in range(e):
                    r[k - e + i] = (r[k - e + i] - f * c[i]) % p
            MUL[x, y] = undig(r[:e])
    NEG = np.array([int(np.where(ADD[x] == 0)[0][0]) for x in range(q)])
    INV = np.array([0] + [int(np.where(MUL[x] == 1)[0][0]) for x in range(1, q)])
    return p, e, ADD, MUL, NEG, INV


class Hex:
    def __init__(self, path):
        with open(path, 'rb') as f:
            q, N, L = struct.unpack('3i', f.read(12))
            lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
            coord = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
        self.q, self.N, self.L = q, N, L
        self.lines, self.coord = lines, coord
        self.p, self.e, self.ADD, self.MUL, self.NEG, self.INV = field(q)
        pl = [[] for _ in range(N)]
        for l in range(L):
            for x in lines[l]:
                pl[x].append(l)
        self.PL = np.array(pl, dtype=np.int64)          # N x (q+1): lines through each point
        w = q ** np.arange(7, dtype=np.int64)
        self.codes = coord @ w
        self.order = np.argsort(self.codes)
        self.sorted_codes = self.codes[self.order]
        # line lookup by its two smallest point ids
        self.line_key = {}
        for l in range(L):
            s = sorted(lines[l])
            self.line_key[(s[0], s[1])] = l

    # ---- vectorised field helpers -------------------------------------------------------------
    def normalize(self, X):
        X = X.copy()
        n = X.shape[0]
        first = np.argmax(X != 0, axis=1)
        lead = X[np.arange(n), first]
        s = self.INV[lead]
        return self.MUL[s[:, None], X]

    def point_ids(self, X):
        Xn = self.normalize(X)
        c = Xn @ (self.q ** np.arange(7, dtype=np.int64))
        idx = np.searchsorted(self.sorted_codes, c)
        idx[idx >= self.N] = 0
        ok = self.sorted_codes[idx] == c
        if not ok.all():
            raise ValueError('image not a point of Q(6,q)')
        return self.order[idx]

    def matvec(self, M, V):
        """M: k x k over GF(q); V: n x k. returns V M^T (rows transformed)."""
        n, k = V.shape
        out = np.zeros((n, M.shape[0]), dtype=np.int64)
        for i in range(M.shape[0]):
            acc = np.zeros(n, dtype=np.int64)
            for j in range(k):
                acc = self.ADD[acc, self.MUL[M[i, j], V[:, j]]]
            out[:, i] = acc
        return out

    def mat_mul(self, A, B):
        return self.matvec(A, B.T).T

    def mat_inv(self, A):
        k = A.shape[0]
        M = np.concatenate([A.copy(), np.eye(k, dtype=np.int64)], axis=1)
        for c in range(k):
            piv = next(r for r in range(c, k) if M[r, c])
            M[[c, piv]] = M[[piv, c]]
            s = self.INV[M[c, c]]
            M[c] = self.MUL[s, M[c]]
            for r in range(k):
                if r != c and M[r, c]:
                    f = self.NEG[M[r, c]]
                    M[r] = self.ADD[M[r], self.MUL[f, M[c]]]
        return M[:, k:]

    def det3(self, A):
        a = A
        t1 = self.MUL[a[0, 0], self.ADD[self.MUL[a[1, 1], a[2, 2]], self.NEG[self.MUL[a[1, 2], a[2, 1]]]]]
        t2 = self.MUL[a[0, 1], self.ADD[self.MUL[a[1, 0], a[2, 2]], self.NEG[self.MUL[a[1, 2], a[2, 0]]]]]
        t3 = self.MUL[a[0, 2], self.ADD[self.MUL[a[1, 0], a[2, 1]], self.NEG[self.MUL[a[1, 1], a[2, 0]]]]]
        return int(self.ADD[self.ADD[t1, self.NEG[t2]], t3])

    # ---- SL(3,q) action on points and lines ---------------------------------------------------
    def sl3_point_map(self, g):
        """permutation of points under (v, a, w) -> (g v, a, g^{-T} w)."""
        gi_t = self.mat_inv(g).T
        X = self.coord
        v = self.matvec(g, X[:, 0:3])
        w = self.matvec(gi_t, X[:, 4:7])
        Y = np.concatenate([v, X[:, 3:4], w], axis=1)
        return self.point_ids(Y)

    def line_map(self, pmap):
        """induced permutation of lines (raises if a line is not mapped to a line)."""
        img = np.empty(self.L, dtype=np.int64)
        for l in range(self.L):
            pts = sorted(pmap[self.lines[l]])
            img[l] = self.line_key[(pts[0], pts[1])]
            if sorted(self.lines[img[l]]) != pts:
                raise ValueError('not a line')
        return img

    # ---- distances in the incidence graph (vertex ids: points 0..N-1, lines N..N+L-1) ----------
    def adjacency(self):
        N = self.N
        adj = np.zeros((N + self.L, self.q + 1), dtype=np.int64)
        adj[:N] = self.PL + N
        adj[N:] = self.lines
        return adj

    def bfs(self, s):
        adj = self.adjacency() if not hasattr(self, '_adj') else self._adj
        self._adj = adj
        n = adj.shape[0]
        d = np.full(n, -1, dtype=np.int64)
        d[s] = 0
        fr = np.array([s])
        k = 0
        while len(fr):
            k += 1
            nb = np.unique(adj[fr].ravel())
            nb = nb[d[nb] < 0]
            d[nb] = k
            fr = nb
        return d
