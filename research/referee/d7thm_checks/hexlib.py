#!/usr/bin/env python3
"""Referee's own construction of the split Cayley hexagon H(q) from the coordinates printed in POLISHED.md §6.1
(q odd: quadric X0X4+X1X5+X2X6 = X3^2) and §6.5 (q even: X0X4+X1X5+X2X6+X3^2 = 0), lines = lines of the quadric
whose Grassmann coordinates satisfy Tits' equations p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
No code of the lab is used."""
import numpy as np, itertools

IRRED = {4: (2, [1, 1, 1]), 8: (2, [1, 1, 0, 1]), 9: (3, [1, 0, 1]), 16: (2, [1, 1, 0, 0, 1]), 25: (5, [2, 0, 1]),
         27: (3, [1, 2, 0, 1])}   # coefficients c0..ce of a monic irreducible polynomial (low degree first)

class GF:
    def __init__(self, q):
        self.q = q
        if q in IRRED:
            p, poly = IRRED[q]; e = len(poly) - 1
        else:
            p, poly, e = q, None, 1
        self.p, self.e = p, e
        def vec(a): return [(a // p**i) % p for i in range(e)]
        def num(v): return sum(c * p**i for i, c in enumerate(v))
        add = np.zeros((q, q), dtype=np.int64); mul = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            for b in range(q):
                va, vb = vec(a), vec(b)
                add[a, b] = num([(x + y) % p for x, y in zip(va, vb)])
                prod = [0] * (2 * e - 1)
                for i, x in enumerate(va):
                    for j, y in enumerate(vb):
                        prod[i + j] = (prod[i + j] + x * y) % p
                if poly is not None:
                    for d in range(2 * e - 2, e - 1, -1):   # reduce x^d = -(c0 + ... + c_{e-1} x^{e-1}) x^{d-e}
                        c = prod[d]
                        if c:
                            prod[d] = 0
                            for i in range(e):
                                prod[d - e + i] = (prod[d - e + i] - c * poly[i]) % p
                mul[a, b] = num(prod[:e])
        self.add, self.mul = add, mul
        self.neg = np.array([int(np.where(add[a] == 0)[0][0]) for a in range(q)])
        self.sub = add[:, self.neg]          # sub[a, b] = a - b
        self.inv = np.zeros(q, dtype=np.int64)
        for a in range(1, q):
            self.inv[a] = int(np.where(mul[a] == 1)[0][0])
        # sanity: field axioms on a sample
        for a, b, c in itertools.product(range(q), repeat=3):
            assert mul[a, add[b, c]] == add[mul[a, b], mul[a, c]]
            assert mul[mul[a, b], c] == mul[a, mul[b, c]]
        self.squares = sorted({int(mul[a, a]) for a in range(q)})
    def tr(self, a):   # absolute trace, char 2
        s, x = 0, a
        for _ in range(self.e):
            s = self.add[s, x]; x = self.mul[x, x]
        return int(s)

def normalize(F, v):
    v = list(v)
    for c in v:
        if c:
            ic = F.inv[c]; return tuple(int(F.mul[ic, x]) for x in v)
    return None

class Hexagon:
    def __init__(self, q):
        F = GF(q); self.F = F; self.q = q; self.even = (q % 2 == 0)
        M, A, S = F.mul, F.add, F.sub
        # points of PG(6,q) on the quadric
        pts = []
        for v in itertools.product(range(q), repeat=7):
            if any(v) and v[[i for i in range(7) if v[i]][0]] == 1:
                Qv = A[A[M[v[0], v[4]], M[v[1], v[5]]], M[v[2], v[6]]]
                Qv = A[Qv, M[v[3], v[3]]] if self.even else S[Qv, M[v[3], v[3]]]
                if Qv == 0: pts.append(v)
        X = np.array(pts, dtype=np.int64); self.X = X; n = len(pts)
        assert n == (q + 1) * (q**4 + q**2 + 1), n
        self.N = n
        self.index = {p: i for i, p in enumerate(pts)}
        # H-lines: for each x, the y with B(x,y) = 0 and Tits' equations on x ^ y
        def pij(x, Y, i, j):
            return S[M[x[i], Y[:, j]], M[x[j], Y[:, i]]]
        lines = {}
        for ix in range(n):
            x = X[ix]
            Bv = A[A[A[A[A[M[x[0], X[:, 4]], M[x[4], X[:, 0]]], M[x[1], X[:, 5]]], M[x[5], X[:, 1]]], M[x[2], X[:, 6]]], M[x[6], X[:, 2]]]
            if not self.even:
                Bv = S[Bv, A[M[x[3], X[:, 3]], M[x[3], X[:, 3]]]]
            cand = np.where(Bv == 0)[0]; cand = cand[cand != ix]
            Y = X[cand]
            ok = (pij(x, Y, 1, 2) == pij(x, Y, 3, 4)) & (pij(x, Y, 5, 4) == pij(x, Y, 3, 2)) & \
                 (pij(x, Y, 2, 0) == pij(x, Y, 3, 5)) & (pij(x, Y, 6, 5) == pij(x, Y, 3, 0)) & \
                 (pij(x, Y, 0, 1) == pij(x, Y, 3, 6)) & (pij(x, Y, 4, 6) == pij(x, Y, 3, 1))
            for iy in cand[ok]:
                if iy < ix: continue
                key = None
                # points of the line <x, y>
                y = X[iy]; L = {ix, int(iy)}
                for t in range(q):
                    w = normalize(F, [A[int(x[c]), M[t, int(y[c])]] for c in range(7)])
                    L.add(self.index[w])
                key = tuple(sorted(L))
                lines[key] = 1
        self.lines = sorted(lines)
        assert len(self.lines) == n, len(self.lines)
        self.on = [[] for _ in range(n)]         # lines through each point
        for li, L in enumerate(self.lines):
            assert len(L) == q + 1
            for p in L: self.on[p].append(li)
        assert all(len(o) == q + 1 for o in self.on)
    def incidence_adj(self):
        n = self.N; adj = [[] for _ in range(2 * n)]
        for li, L in enumerate(self.lines):
            for p in L: adj[p].append(n + li); adj[n + li].append(p)
        return adj

def bfs(adj, s):
    d = {s: 0}; fr = [s]
    while fr:
        nf = []
        for u in fr:
            for w in adj[u]:
                if w not in d: d[w] = d[u] + 1; nf.append(w)
        fr = nf
    return d

def dist_array(adj, s):
    n = len(adj); d = np.full(n, -1, dtype=np.int64); d[s] = 0; fr = [s]; t = 0
    while fr:
        t += 1; nf = []
        for u in fr:
            for w in adj[u]:
                if d[w] < 0: d[w] = t; nf.append(w)
        fr = nf
    return d
