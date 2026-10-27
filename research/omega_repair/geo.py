"""Split Cayley hexagon H(q) in Q(6,q) (as built by hexq6.c: X0X4 + X1X5 + X2X6 = X3^2, Tits' line equations) and its
collineations as 7x7 matrices.  Field encoding as in hexq6.c: q prime -> integers mod q; q = 4, 8 -> polynomial basis
(x^2+x+1, x^3+x+1), integer = bit vector; q = 9 -> a + b i (i^2 = -1) encoded a + 3b.

Used by every other script in this folder.  Every matrix is checked to map every hexagon line onto a hexagon line
before its permutation is returned (H.perm(M) raises otherwise)."""
import numpy as np


class GF:
    def __init__(self, q):
        self.q = q
        if q in (4, 8):
            self.p, poly = 2, (7 if q == 4 else 11)
            add = [[x ^ y for y in range(q)] for x in range(q)]
            mul = [[0] * q for _ in range(q)]
            for x in range(q):
                for y in range(q):
                    r, a, b = 0, x, y
                    while b:
                        if b & 1:
                            r ^= a
                        b >>= 1; a <<= 1
                        if a & q:
                            a ^= poly
                    mul[x][y] = r
        elif q == 9:
            self.p = 3
            add = [[(x % 3 + y % 3) % 3 + 3 * ((x // 3 + y // 3) % 3) for y in range(9)] for x in range(9)]
            mul = [[((x % 3) * (y % 3) - (x // 3) * (y // 3)) % 3 + 3 * (((x % 3) * (y // 3) + (x // 3) * (y % 3)) % 3)
                    for y in range(9)] for x in range(9)]
        else:
            self.p = q
            add = [[(x + y) % q for y in range(q)] for x in range(q)]
            mul = [[x * y % q for y in range(q)] for x in range(q)]
        self.ADD = np.array(add, dtype=np.int64); self.MUL = np.array(mul, dtype=np.int64)
        self.NEG = np.array([add[x].index(0) for x in range(q)]); self.INV = np.array([mul[x].index(1) if x else 0 for x in range(q)])
        self.frob = np.array([self.pw(x, self.p) for x in range(q)])

    def pw(self, x, e):
        r = 1
        for _ in range(e):
            r = int(self.MUL[r, x])
        return r

    def mm(self, A, B):                       # matrix product (works on 2-d int arrays)
        A = np.asarray(A); B = np.asarray(B)
        C = np.zeros((A.shape[0], B.shape[1]), dtype=np.int64)
        for i in range(A.shape[1]):
            C = self.ADD[C, self.MUL[A[:, i:i + 1], B[i:i + 1, :]]]
        return C

    def inv(self, A):
        m = A.shape[0]; M = np.concatenate([np.array(A, dtype=np.int64), np.eye(m, dtype=np.int64)], axis=1)
        for c in range(m):
            r = next(r for r in range(c, m) if M[r, c]); M[[c, r]] = M[[r, c]]; M[c] = self.MUL[self.INV[M[c, c]], M[c]]
            for r in range(m):
                if r != c and M[r, c]:
                    M[r] = self.ADD[M[r], self.MUL[self.NEG[M[r, c]], M[c]]]
        return M[:, m:]


class Hex:
    def __init__(self, path):
        f = open(path); self.q, self.n, nl = map(int, f.readline().split())
        self.L = np.array([list(map(int, f.readline().split())) for _ in range(nl)], dtype=np.int64)
        self.P = np.array([list(map(int, f.readline().split()[1:])) for _ in range(self.n)], dtype=np.int64)
        q, n = self.q, self.n; self.F = F = GF(q)
        self.pwv = q ** np.arange(6, -1, -1)
        self.lut = -np.ones(q ** 7, dtype=np.int64); self.lut[(self.P * self.pwv).sum(1)] = np.arange(n)
        Ls = np.sort(self.L, 1); self.Lkey = {(int(r[0]), int(r[1])): i for i, r in enumerate(Ls)}
        self.Ls = Ls
        self.lines_of = [[] for _ in range(n)]
        for i, r in enumerate(self.L):
            for p in r:
                self.lines_of[p].append(i)

    def normalize(self, X):
        F = self.F; X = X.copy(); first = (X != 0).argmax(1); s = F.INV[X[np.arange(len(X)), first]]
        return F.MUL[X, s[:, None]]

    def B(self, x, y):                       # polar form of X0X4 + X1X5 + X2X6 - X3^2
        F = self.F; A, M = F.ADD, F.MUL
        s = A[M[x[0], y[4]], M[x[4], y[0]]]; s = A[s, A[M[x[1], y[5]], M[x[5], y[1]]]]; s = A[s, A[M[x[2], y[6]], M[x[6], y[2]]]]
        t = M[x[3], y[3]]; return A[s, F.NEG[A[t, t]]]

    def perm(self, M, frob=0):
        """point and line permutations of x -> M x^(p^frob); raises if a line is not mapped to a line"""
        X = self.P
        for _ in range(frob):
            X = self.F.frob[X]
        Y = self.normalize(self.F.mm(X, np.asarray(M).T)); pp = self.lut[(Y * self.pwv).sum(1)]
        assert (pp >= 0).all(), "a point is not mapped to a point"
        img = np.sort(pp[self.L], 1)
        lp = np.array([self.Lkey.get((int(r[0]), int(r[1])), -1) for r in img])
        if (lp < 0).any() or not (self.Ls[lp] == img).all():
            raise ValueError("not a collineation")
        assert len(set(pp.tolist())) == self.n and len(set(lp.tolist())) == self.n
        return pp, lp

    def is_coll(self, M):
        try:
            self.perm(M); return True
        except ValueError:
            return False

    def sl3(self, A):
        M = np.zeros((7, 7), dtype=np.int64); M[:3, :3] = A; M[3, 3] = 1; M[4:, 4:] = self.F.inv(np.array(A)).T
        return M

    def siegel(self, u, v):
        """x -> x + B(x,u) v - B(x,v) u (an isometry of Q(6,q) when <u,v> is totally singular)"""
        F = self.F; M = np.eye(7, dtype=np.int64)
        for j in range(7):
            e = np.zeros(7, dtype=np.int64); e[j] = 1
            a, b = self.B(e, u), self.B(e, v)
            col = F.ADD[F.ADD[e, F.MUL[a, v]], F.MUL[F.NEG[b], u]]
            M[:, j] = col
        return M
