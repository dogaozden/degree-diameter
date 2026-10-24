#!/usr/bin/env python3
"""Fast split Cayley hexagon H(q) (job cell-12-7). Same model as polygons.py (theorem-search branch):
points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q), lines = lines of the quadric whose Grassmann coordinates satisfy
Tits' equations p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
Instead of testing all point pairs, for each point x the six equations and B(x,y)=0 are linear in y; their solution
space W_x is the plane spanned by the q+1 hexagon lines through x. Cost O(#points * q^2).

usage: python3 gh_fast.py q OUT      writes polygons.py format: first line P, then one line per hexagon line with
                                      its q+1 point ids (points 0..P-1, lines indexed by file order).
       python3 gh_fast.py q OUT check  also checks diameter 6 / girth 12 from a point and a line (BFS).
"""
import itertools, sys
from collections import deque

IRRED = {4: (2, [1, 1]), 8: (2, [1, 1, 0]), 9: (3, [1, 0]), 16: (2, [1, 1, 0, 0]), 25: (5, [2, 0]),
         27: (3, [1, 2, 0]), 49: (7, [1, 0])}   # x^n = -(c0 + c1 x + ...): q = p^n, coefficients of the monic poly


class GF:
    def __init__(self, q):
        self.q = q
        primes = [p for p in range(2, q + 1) if all(p % d for d in range(2, p)) and q % p == 0]
        p = primes[0]; n = 0; t = q
        while t > 1:
            t //= p; n += 1
        self.p, self.n = p, n
        if n == 1:
            self.add = [[(a + b) % p for b in range(q)] for a in range(q)]
            self.mul = [[(a * b) % p for b in range(q)] for a in range(q)]
        else:
            pp, c = IRRED[q]          # c: x^n + c[n-1] x^(n-1) + ... + c[0] = 0  (list c0..c_{n-1})
            assert pp == p
            def vec(a): return [(a // p ** k) % p for k in range(n)]
            def num(v): return sum(v[k] * p ** k for k in range(n))
            def mulv(u, v):
                prod = [0] * (2 * n - 1)
                for i in range(n):
                    for j in range(n):
                        prod[i + j] = (prod[i + j] + u[i] * v[j]) % p
                for d in range(2 * n - 2, n - 1, -1):     # reduce x^d = x^(d-n) * x^n = -x^(d-n) * sum c_k x^k
                    co = prod[d]
                    if co:
                        prod[d] = 0
                        for k in range(n):
                            prod[d - n + k] = (prod[d - n + k] - co * c[k]) % p
                return prod[:n]
            self.add = [[num([(x + y) % p for x, y in zip(vec(a), vec(b))]) for b in range(q)] for a in range(q)]
            self.mul = [[num(mulv(vec(a), vec(b))) for b in range(q)] for a in range(q)]
        self.neg = [next(b for b in range(q) if self.add[a][b] == 0) for a in range(q)]
        self.inv = [0] + [next(b for b in range(q) if self.mul[a][b] == 1) for a in range(1, q)]
        # field sanity: every nonzero element invertible, mult associative on a sample
        assert all(self.mul[a][self.inv[a]] == 1 for a in range(1, q))

    def sub(self, a, b):
        return self.add[a][self.neg[b]]


def normalize(F, v):
    for x in v:
        if x:
            s = F.inv[x]
            return tuple(F.mul[s][c] for c in v)
    raise ValueError('zero vector')


def nullspace(F, rows, ncols):
    """basis of {y : r.y = 0 for r in rows} over GF(q)"""
    A = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(A)) if A[i][c]), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        s = F.inv[A[r][c]]
        A[r] = [F.mul[s][x] for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [F.sub(A[i][k], F.mul[f][A[r][k]]) for k in range(ncols)]
        piv.append(c); r += 1
        if r == len(A):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        y = [0] * ncols; y[fc] = 1
        for i, pc in enumerate(piv):
            y[pc] = F.neg[A[i][fc]]
        basis.append(y)
    return basis


def hexagon(q):
    F = GF(q)
    A, M, S = F.add, F.mul, F.sub
    def Qf(v):
        return S(A[A[M[v[0]][v[4]]][M[v[1]][v[5]]]][M[v[2]][v[6]]], M[v[3]][v[3]])
    pts = [v for v in itertools.product(range(q), repeat=7) if next((c for c in v if c), 0) == 1 and Qf(v) == 0]
    P = len(pts)
    assert P == (q ** 6 - 1) // (q - 1), P
    index = {v: i for i, v in enumerate(pts)}
    two = A[1][1]
    pairs = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    lines = {}
    for x in pts:
        rows = []
        # polar form B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 - 2 x3y3
        r = [0] * 7
        r[4] = A[r[4]][x[0]]; r[0] = A[r[0]][x[4]]; r[5] = A[r[5]][x[1]]; r[1] = A[r[1]][x[5]]
        r[6] = A[r[6]][x[2]]; r[2] = A[r[2]][x[6]]; r[3] = S(r[3], M[two][x[3]])
        rows.append(r)
        for (a, b), (c, d) in pairs:     # p_ab - p_cd = 0, p_ab(x,y) = x_a y_b - x_b y_a
            r = [0] * 7
            r[b] = A[r[b]][x[a]]; r[a] = S(r[a], x[b])
            r[d] = S(r[d], x[c]); r[c] = A[r[c]][x[d]]
            rows.append(r)
        W = nullspace(F, rows, 7)
        assert len(W) == 3, (x, len(W))
        # basis {x, w1, w2} of W: pick two vectors of W independent of x
        cand = []
        for w in W:
            M2 = [list(x)] + cand + [w]
            if len(nullspace(F, list(zip(*M2)), len(M2))) == 0:   # columns independent
                cand.append(w)
            if len(cand) == 2:
                break
        w1, w2 = cand
        dirs = [w2] + [[A[w1[k]][M[t][w2[k]]] for k in range(7)] for t in range(q)]
        for w in dirs:
            mem = {index[normalize(F, x)]}
            for a in range(q):
                v = [A[w[k]][M[a][x[k]]] for k in range(7)]
                mem.add(index[normalize(F, v)])
            key = frozenset(mem)
            assert len(key) == q + 1
            lines[key] = 1
    L = [sorted(s) for s in lines]
    assert len(L) == P, (len(L), P)
    deg = [0] * P
    for l in L:
        for p in l:
            deg[p] += 1
    assert all(d == q + 1 for d in deg)
    return P, L


def check(P, L, n=6):
    V = 2 * P
    adj = [[] for _ in range(V)]
    for k, l in enumerate(L):
        for p in l:
            adj[p].append(P + k); adj[P + k].append(p)
    out = []
    for s in (0, P):
        dist = [-1] * V; dist[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1; dq.append(w)
        assert min(dist) >= 0
        out.append(max(dist))
    return out


if __name__ == '__main__':
    q = int(sys.argv[1]); out = sys.argv[2]
    P, L = hexagon(q)
    with open(out, 'w') as f:
        f.write(f"{P}\n")
        for l in L:
            f.write(' '.join(map(str, l)) + '\n')
    msg = f"H({q}): points {P}, lines {len(L)}, {q+1} points per line, {q+1} lines per point"
    if len(sys.argv) > 3:
        msg += f", eccentricity from a point and a line {check(P, L)}"
    print(msg)
