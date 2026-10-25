"""The split Cayley hexagon H(q) from coordinates, independent of the lab's hexagon generators.

Points: all points of the parabolic quadric Q(6,q): X0 X4 + X1 X5 + X2 X6 = X3^2 in PG(6,q).
Lines:  the lines of Q(6,q) whose Grassmann coordinates p_ij = x_i y_j - x_j y_i satisfy Tits' equations
        p12 = p34, p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31
        (the form quoted from memory as Van Maldeghem 2.4.13, p20 = p36 and p01 = p35, gives 1 + q collinear points for
        some points, not 1 + q(q+1); the version above is the one invariant under the torus t0 t1 t2 = 1,
        t_{i+4} = 1/t_i, t3 = 1, and it is validated below for q = 2, 3, 4, 5).
Element ids: points 0..N-1, lines N..2N-1 (N = (q^6-1)/(q-1)); the incidence graph is written as an apsp edge list.

Usage: python3 hexq.py Q          builds, validates and caches cache/hexQ.npz (+ cache/hexQ.edges, cache/hexQ.dist)
"""
import itertools, os, subprocess, sys, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, 'cache')

IRRED = {4: (2, [1, 1, 1]), 8: (2, [1, 1, 0, 1]), 9: (3, [1, 0, 1])}   # coefficients c0 + c1 x + ... (monic)


def gf_tables(q):
    """add, mul, neg, inv tables of GF(q); elements are ints 0..q-1 (base-p digits = polynomial coefficients)."""
    if q in IRRED:
        p, poly = IRRED[q]
        e = len(poly) - 1
    else:
        p, e, poly = q, 1, None
    digits = [[(x // p ** i) % p for i in range(e)] for x in range(q)]
    def enc(d):
        return sum(int(d[i]) * p ** i for i in range(e))
    add = np.zeros((q, q), dtype=np.int64)
    mul = np.zeros((q, q), dtype=np.int64)
    for a in range(q):
        for b in range(q):
            add[a, b] = enc([(digits[a][i] + digits[b][i]) % p for i in range(e)])
            prod = [0] * (2 * e - 1)
            for i in range(e):
                for j in range(e):
                    prod[i + j] += digits[a][i] * digits[b][j]
            prod = [x % p for x in prod]
            if poly is not None:
                for k in range(2 * e - 2, e - 1, -1):      # reduce x^k = -(c0 + ... + c_{e-1} x^{e-1}) x^{k-e}
                    co = prod[k]
                    if co:
                        prod[k] = 0
                        for i in range(e):
                            prod[k - e + i] = (prod[k - e + i] - co * poly[i]) % p
            mul[a, b] = enc(prod[:e])
    neg = np.array([int(np.where(add[a] == 0)[0][0]) for a in range(q)])
    inv = np.zeros(q, dtype=np.int64)
    for a in range(1, q):
        inv[a] = int(np.where(mul[a] == 1)[0][0])
    return p, add, mul, neg, inv


class GF:
    def __init__(self, q):
        self.q = q
        self.p, self.A, self.M, self.N_, self.I = gf_tables(q)

    def add(self, a, b): return self.A[a, b]
    def mul(self, a, b): return self.M[a, b]
    def neg(self, a): return self.N_[a]
    def sub(self, a, b): return self.A[a, self.N_[b]]


def normalize(F, X):
    """scale rows of X (n x 7 int) so the first nonzero coordinate is 1"""
    X = np.asarray(X)
    first = np.argmax(X != 0, axis=1)
    lead = X[np.arange(len(X)), first]
    return F.M[F.I[lead][:, None], X]


def encode(q, X):
    return (X * (q ** np.arange(7))).sum(axis=1)


def quad(F, X):
    """Q(x) = x0x4 + x1x5 + x2x6 - x3^2"""
    s = F.A[F.A[F.M[X[:, 0], X[:, 4]], F.M[X[:, 1], X[:, 5]]], F.M[X[:, 2], X[:, 6]]]
    return F.A[s, F.N_[F.M[X[:, 3], X[:, 3]]]]


def polar(F, x, Y):
    """B(x, y) = x0y4 + x4y0 + x1y5 + x5y1 + x2y6 + x6y2 - 2 x3y3 for one x and all rows y of Y"""
    t = np.zeros(len(Y), dtype=np.int64)
    for i, j in [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]:
        t = F.A[t, F.M[x[i], Y[:, j]]]
    two = F.A[1, 1]
    return F.A[t, F.N_[F.M[F.M[two, x[3]], Y[:, 3]]]]


TITS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def grass(F, x, Y, i, j):
    return F.A[F.M[x[i], Y[:, j]], F.N_[F.M[x[j], Y[:, i]]]]


def build(q, tits=TITS):
    F = GF(q)
    t0 = time.time()
    allv = np.array(list(itertools.product(range(q), repeat=7)), dtype=np.int64)[:, ::-1]   # x0 varies slowest... any order
    allv = allv[(allv != 0).any(axis=1)]
    first = np.argmax(allv != 0, axis=1)
    allv = allv[allv[np.arange(len(allv)), first] == 1]
    pts = allv[quad(F, allv) == 0]
    N = (q ** 6 - 1) // (q - 1)
    assert len(pts) == N, (len(pts), N)
    codes = encode(q, pts)
    order = np.argsort(codes)
    pts, codes = pts[order], codes[order]
    def idx(X):
        c = encode(q, normalize(F, X))
        k = np.searchsorted(codes, c)
        assert (codes[k] == c).all()
        return k
    lines = {}
    for a in range(N):
        x = pts[a]
        Y = pts[polar(F, x, pts) == 0]
        ok = np.ones(len(Y), dtype=bool)
        for (i, j), (k, l) in tits:
            ok &= grass(F, x, Y, i, j) == grass(F, x, Y, k, l)
        Y = Y[ok]
        Y = Y[(Y != x).any(axis=1)]
        ids = idx(Y)
        seen = set()
        for y, iy in zip(Y, ids):
            if iy in seen:
                continue
            # points of the line xy: x and y + t x
            L = [a] + [int(v) for v in idx(F.A[y[None, :].repeat(q, 0), F.M[np.arange(q)[:, None], x[None, :]]])]
            seen.update(L)
            lines[tuple(sorted(L))] = 1
    lines = np.array(sorted(lines), dtype=np.int64)
    return F, pts, lines, time.time() - t0


def incidence_edges(N, lines):
    e = []
    for li, L in enumerate(lines):
        for p in L:
            e.append((int(p), N + li))
    return e


def write_edges(path, n, edges):
    with open(path, 'w') as f:
        f.write(f'{n}\n')
        f.write(''.join(f'{a} {b}\n' for a, b in edges))


class Hex:
    """cached H(q): pts (N x 7), lines (N x (q+1) point ids), point_lines (N x (q+1) line ids, as element ids N+..),
    dist (2N x 2N uint8 incidence-graph distances; elements: points 0..N-1, lines N..2N-1)."""
    def __init__(self, q, with_dist=True):
        z = np.load(os.path.join(CACHE, f'hex{q}.npz'))
        self.q, self.pts, self.lines = q, z['pts'], z['lines']
        self.N = len(self.pts)
        self.F = GF(q)
        N = self.N
        pl = [[] for _ in range(N)]
        for li, L in enumerate(self.lines):
            for p in L:
                pl[p].append(N + li)
        self.point_lines = np.array(pl, dtype=np.int64)
        self.nbr = np.zeros((2 * N, q + 1), dtype=np.int64)        # incidence neighbours of every element
        self.nbr[:N] = self.point_lines
        self.nbr[N:] = self.lines
        if with_dist:
            self.dist = np.fromfile(os.path.join(CACHE, f'hex{q}.dist'), dtype=np.uint8).reshape(2 * N, 2 * N)

    def line_through(self, p, x):
        """the line (element id) through two collinear points"""
        s = set(self.point_lines[p]) & set(self.point_lines[x])
        assert len(s) == 1
        return s.pop()

    def mid(self, a, b):
        """the midpoint of the unique geodesic from a to b (d(a, b) = 2 or 4)"""
        k = int(self.dist[a, b])
        assert k in (2, 4)
        s = np.where((self.dist[a] == k // 2) & (self.dist[b] == k // 2))[0]
        assert len(s) == 1
        return int(s[0])

    def common(self, a, b):
        """the unique element adjacent to both a and b (d(a, b) = 2)"""
        s = set(self.nbr[a]) & set(self.nbr[b])
        assert len(s) == 1
        return s.pop()


def make(q):
    F, pts, lines, dt = build(q)
    N = len(pts)
    os.makedirs(CACHE, exist_ok=True)
    np.savez(os.path.join(CACHE, f'hex{q}.npz'), pts=pts, lines=lines)
    print(f'q={q}: {N} points, {len(lines)} lines from Tits equations ({dt:.1f}s)')
    ep = os.path.join(CACHE, f'hex{q}.edges')
    write_edges(ep, 2 * N, incidence_edges(N, lines))
    return F, pts, lines


def validate(q, full=True):
    H = Hex(q, with_dist=False)
    N, F = H.N, H.F
    res = []
    res.append(('points', N == (q ** 6 - 1) // (q - 1)))
    res.append(('lines', len(H.lines) == N))
    res.append(('q+1 points per line', H.lines.shape[1] == q + 1))
    cnt = np.bincount(H.lines.ravel(), minlength=N)
    res.append(('q+1 lines per point', (cnt == q + 1).all()))
    # every H-line is a totally singular line of Q(6,q): checked through q+1 points on the quadric (by construction) and
    # pairwise orthogonality
    if full:
        ep = os.path.join(CACHE, f'hex{q}.edges')
        dp = os.path.join(CACHE, f'hex{q}.dist')
        subprocess.run([os.path.join(HERE, 'dist'), ep, dp], check=True)
        D = np.fromfile(dp, dtype=np.uint8).reshape(2 * N, 2 * N)
        res.append(('incidence graph connected, diameter 6', int(D.max()) == 6))
        # girth 12: no two elements at distance d < 6 joined by two geodesics; equivalently every vertex has exactly
        # (q+1) q^(k-1) vertices at distance k for k = 1..5 (Moore-type count) and the rest at distance 6
        ok = True
        for s in range(0, 2 * N, max(1, (2 * N) // 500) if q > 4 else 1):
            h = np.bincount(D[s], minlength=7)
            want = [1] + [(q + 1) * q ** (k - 1) for k in range(1, 6)] + [q ** 5]
            ok &= list(h[:7]) == want
        res.append(('distance profile 1,(q+1),(q+1)q,...,(q+1)q^4,q^5 (girth 12)', bool(ok)))
        # points: distance <= 4 iff orthogonal for the polar form
        ok = True
        rows = range(N) if q <= 4 else range(0, N, max(1, N // 300))
        for a in rows:
            B = polar(F, H.pts[a], H.pts)
            ok &= bool(((D[a, :N] <= 4) == (B == 0)).all())
        res.append(('points: incidence distance <= 4 iff orthogonal', ok))
    for name, ok in res:
        print(f'  {"OK  " if ok else "FAIL"} {name}')
    return all(ok for _, ok in res)


def hermitian_spread(H):
    """H(q)-lines inside a hyperplane x0 = c x4 + e x3 whose section of Q(6,q) is elliptic; returns (c, e, line ids)."""
    q, F, N = H.q, H.F, H.N
    want = (q + 1) * (q ** 3 + 1)
    for c in range(q):
        for e in range(q):
            h = F.A[H.pts[:, 0], F.N_[F.A[F.M[c, H.pts[:, 4]], F.M[e, H.pts[:, 3]]]]] == 0
            if h.sum() != want:
                continue
            inside = h[H.lines].all(axis=1)
            ids = N + np.where(inside)[0]
            if len(ids) == q ** 3 + 1:
                return c, e, ids
    return None


if __name__ == '__main__':
    q = int(sys.argv[1])
    make(q)
    ok = validate(q, full=q <= 5)
    print('VALID' if ok else 'INVALID')
