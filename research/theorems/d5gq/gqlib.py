"""Generalized quadrangles for the D = 5 note (research/theorems/D5_QUADRANGLE.md).

A GQ object has points 0..np-1, lines 0..nl-1, `lines[l]` = tuple of points, `plines[p]` = tuple of lines.
Constructors: W(q) (symplectic), Q4(q) (dual of W(q)), Q5(q) (elliptic quadric Q^-(5,q)), H3(q) (dual of Q5(q)),
AS(q) (Payne derivative of W(q) at a point; isomorphic to AS(q) for q odd), T2(q, oval) (Tits, q even).
Distances in the incidence graph: dpp[p,p'] in {0,2,4}, dll[l,l'] in {0,2,4}, dpl[p,l] in {1,3}.
"""
import sys, os, itertools
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'chartlift'))
from gf import GF


class GQ:
    def __init__(self, name, lines, npts, coords=None, lcoords=None):
        self.name = name
        self.lines = [tuple(sorted(l)) for l in lines]
        self.np = npts
        self.nl = len(self.lines)
        pl = [[] for _ in range(npts)]
        for i, l in enumerate(self.lines):
            for p in l:
                pl[p].append(i)
        self.plines = [tuple(x) for x in pl]
        self.coords = coords      # point coordinates (if any)
        self.lcoords = lcoords
        self.s = len(self.lines[0]) - 1
        self.t = len(self.plines[0]) - 1
        self._dist()

    def _dist(self):
        n, m = self.np, self.nl
        I = np.zeros((n, m), dtype=np.int32)
        for i, l in enumerate(self.lines):
            I[list(l), i] = 1
        self.I = I
        C = (I @ I.T) > 0          # collinear or equal
        K = (I.T @ I) > 0          # concurrent or equal
        self.col = C.copy(); np.fill_diagonal(self.col, False)
        self.con = K.copy(); np.fill_diagonal(self.con, False)
        dpp = np.full((n, n), 4, dtype=np.int8); dpp[C] = 2; np.fill_diagonal(dpp, 0)
        dll = np.full((m, m), 4, dtype=np.int8); dll[K] = 2; np.fill_diagonal(dll, 0)
        dpl = np.full((n, m), 3, dtype=np.int8); dpl[I > 0] = 1
        self.dpp, self.dll, self.dpl = dpp, dll, dpl

    def check(self):
        """GQ axioms via the incidence graph: (s+1)/(t+1) biregular, every point-line pair at distance <= 3, girth 8."""
        s, t = self.s, self.t
        assert all(len(l) == s + 1 for l in self.lines) and all(len(x) == t + 1 for x in self.plines)
        assert self.np == (s + 1) * (s * t + 1) and self.nl == (t + 1) * (s * t + 1)
        # two collinear points lie on exactly one common line (no digons), no triangles:
        IIt = self.I @ self.I.T
        off = IIt[~np.eye(self.np, dtype=bool)]
        assert off.max() <= 1
        # GQ axiom: a point p not on line l is collinear with exactly one point of l
        A = self.col.astype(np.int32) @ self.I        # A[p,l] = # points of l collinear with p (p not on l)
        assert np.all(A[self.I == 0] == 1)
        return True

    def dual(self, name=None):
        return GQ(name or (self.name + '^D'), [self.plines[p] for p in range(self.np)], self.nl,
                  coords=self.lcoords, lcoords=self.coords)

    def perp(self, p):
        return np.nonzero(self.col[p])[0]


def _points(F, dim):
    """normalized representatives of PG(dim-1, q): first nonzero coordinate = 1"""
    q = F.q
    pts = []
    for v in itertools.product(range(q), repeat=dim):
        nz = [x for x in v if x]
        if nz and nz[0] == 1:
            pts.append(v)
    return pts


def _norm(F, v):
    for x in v:
        if x:
            s = F.inv[x]
            return tuple(F.mul[s][y] for y in v)
    raise ValueError


def _span_line(F, a, b, index):
    """points of the projective line <a,b> as indices"""
    out = {index[_norm(F, a)]}
    for lam in range(F.q):
        v = tuple(F.add[F.mul[lam][x]][y] for x, y in zip(a, b))
        out.add(index[_norm(F, v)])
    return tuple(sorted(out))


def W(q):
    """W(q): points of PG(3,q), lines totally isotropic for w(x,y) = x0y2 + x1y3 - x2y0 - x3y1."""
    F = GF(q)
    pts = _points(F, 4)
    index = {v: i for i, v in enumerate(pts)}
    def w(x, y):
        a = F.add[F.mul[x[0]][y[2]]][F.mul[x[1]][y[3]]]
        b = F.add[F.mul[x[2]][y[0]]][F.mul[x[3]][y[1]]]
        return F.sub[a][b]
    n = len(pts)
    seen = set(); lines = []
    for i in range(n):
        for j in range(i + 1, n):
            if w(pts[i], pts[j]) == 0:
                key = (i, j)
                if key in seen:
                    continue
                l = _span_line(F, pts[i], pts[j], index)
                for a, b in itertools.combinations(l, 2):
                    seen.add((a, b))
                lines.append(l)
    G = GQ('W(%d)' % q, lines, n, coords=pts)
    G.F = F; G.form = w; G.index = index
    return G


def Q4(q):
    G = W(q).dual('Q(4,%d)' % q)
    return G


def Q5(q):
    """Q^-(5,q): x0x1 + x2x3 + f(x4,x5) = 0 with f anisotropic (x4^2 + b x4x5 + c x5^2 irreducible)."""
    F = GF(q)
    b, c = next((b, c) for b in range(q) for c in range(q)
                if all(F.add[F.add[F.mul[x][x]][F.mul[b][x]]][c] != 0 for x in range(q)))
    def Q(v):
        t = F.add[F.mul[v[0]][v[1]]][F.mul[v[2]][v[3]]]
        f = F.add[F.add[F.mul[v[4]][v[4]]][F.mul[b][F.mul[v[4]][v[5]]]]][F.mul[c][F.mul[v[5]][v[5]]]]
        return F.add[t][f]
    pts = [v for v in _points(F, 6) if Q(v) == 0]
    index = {v: i for i, v in enumerate(pts)}
    n = len(pts)
    seen = set(); lines = []
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) in seen:
                continue
            a, bb = pts[i], pts[j]
            # line on the quadric iff all its points are on it
            ok = True; l = {i, j}
            for lam in range(q):
                v = _norm(F, tuple(F.add[F.mul[lam][x]][y] for x, y in zip(a, bb)))
                if Q(v) != 0:
                    ok = False; break
                l.add(index[v])
            if ok:
                l = tuple(sorted(l))
                for x, y in itertools.combinations(l, 2):
                    seen.add((x, y))
                lines.append(l)
    G = GQ('Q(5,%d)' % q, lines, n, coords=pts)
    G.F = F
    return G


def H3(q):
    return Q5(q).dual('H(3,%d)' % (q * q))


def AS(q):
    """Payne derivative P(W(q), x) at x = point 0: points not collinear with x; lines = lines of W(q) missing x^perp-points
    removed... precisely: lines of W(q) not through x (minus their point in x^perp), and hyperbolic lines {x,y}^perp-perp
    minus x.  Order (q-1, q+1); for q odd this is AS(q)."""
    Wq = W(q)
    x = 0
    far = [p for p in range(Wq.np) if p != x and not Wq.col[x, p]]
    idx = {p: i for i, p in enumerate(far)}
    lines = []
    for l in Wq.lines:
        if x in l:
            continue
        lines.append(tuple(idx[p] for p in l if p in idx))
    seen = set()
    for y in far:
        if y in seen:
            continue
        cent = np.nonzero(Wq.col[x] & Wq.col[y])[0]           # {x,y}^perp
        hyp = np.nonzero(np.all(Wq.col[:, cent] | (np.arange(Wq.np)[:, None] == cent[None, :]), axis=1))[0]
        hyp = [p for p in hyp if p != x]                       # {x,y}^perp-perp minus x
        for p in hyp:
            seen.add(p)
        lines.append(tuple(idx[p] for p in hyp))
    return GQ('AS(%d)' % q, lines, len(far))


def regular_spread_W(G):
    """A regular spread of W(q) (form x0y2 + x1y3 - x2y0 - x3y1): L(inf) = <e2,e3> and L(A) = {(u, uA)} for the q^2
    symmetric matrices A = [[a, b], [b, alpha*a + beta*b]] with x^2 - beta x - alpha irreducible.  Returns line ids."""
    F = G.F; q = F.q
    alpha, beta = next((al, be) for al in range(q) for be in range(q)
                       if all(F.sub[F.sub[F.mul[x][x]][F.mul[be][x]]][al] != 0 for x in range(q)))
    lid = {l: i for i, l in enumerate(G.lines)}
    out = [lid[_span_line(F, (0, 0, 1, 0), (0, 0, 0, 1), G.index)]]
    for a in range(q):
        for b in range(q):
            c = F.add[F.mul[alpha][a]][F.mul[beta][b]]
            # rows (1,0 | a,b) and (0,1 | b,c)
            out.append(lid[_span_line(F, (1, 0, a, b), (0, 1, b, c), G.index)])
    S = sorted(set(out))
    assert len(S) == q * q + 1
    return S


def is_partial_ovoid(G, R):
    R = list(R)
    return not G.col[np.ix_(R, R)].any()


def is_partial_spread(G, R):
    R = list(R)
    return not G.con[np.ix_(R, R)].any()


if __name__ == '__main__':
    for q in (2, 3, 4, 5):
        G = W(q); G.check(); D = G.dual(); D.check()
        S = regular_spread_W(G); assert is_partial_spread(G, S)
        print(G.name, G.np, G.nl, 'order', (G.s, G.t), 'spread', len(S), 'ok')
    for q in (2, 3):
        G = Q5(q); G.check(); print(G.name, G.np, G.nl, (G.s, G.t), 'ok'); H = G.dual(); H.check()
    for q in (3, 5):
        G = AS(q); G.check(); print(G.name, G.np, G.nl, (G.s, G.t), 'ok')
