"""W(3,q) in F^4 coordinates with a symplectic semifield spread (Kantor-Knuth family).

Points: normalised nonzero (x1,x2,y1,y2) over F = GF(q). Form <(x,y),(x',y')> = x.y'^T - y.x'^T.
Spread set Sigma_sigma = {M(a,b) = [[a, b], [b, eta a^sigma]]}: eta a nonsquare, sigma = x -> x^(p^e).
Spread lines: {(x, x M) : x in F^2} for M in Sigma, and {(0, y)}. sigma = id gives the regular spread;
sigma != id (q = p^h, h > 1) gives the Kantor-Knuth spread (dual: the Kantor ovoid of Q(4,q)).
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402


class W3F:
    def __init__(self, q, e=0):
        F = lib.GF(q)
        self.q, self.F = q, F
        add, mul = F.add, F.mul
        p = F.p
        sig = (lambda a: F.pow(a, p ** e) if a else 0) if e else (lambda a: a)
        squares = {mul(x, x) for x in range(1, q)}
        eta = next(x for x in range(1, q) if x not in squares)

        def norm(v):
            for c in v:
                if c:
                    inv = F.inv(c)
                    return tuple(mul(inv, y) for y in v)
        pts = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
        idx = {v: i for i, v in enumerate(pts)}
        n = len(pts)
        self.pts, self.idx = pts, idx

        def form(u, v):
            return F.sub(add(mul(u[0], v[2]), mul(u[1], v[3])), add(mul(u[2], v[0]), mul(u[3], v[1])))

        def span(u, v):
            S = {idx[norm(u)], idx[norm(v)]}
            for lam in range(1, q):
                S.add(idx[norm(tuple(add(u[k], mul(lam, v[k])) for k in range(4)))])
            return tuple(sorted(S))
        lines = set()
        for i in range(n):
            u = pts[i]
            for j in range(i + 1, n):
                if form(u, pts[j]) == 0:
                    lines.add(span(u, pts[j]))
        lines = sorted(lines)
        assert len(lines) == n
        self.lines = lines
        spread = [span((0, 0, 1, 0), (0, 0, 0, 1))]
        for a in range(q):
            for b in range(q):
                # rows of [I | M]: (1,0,a,b), (0,1,b,eta a^sigma)
                spread.append(span((1, 0, a, b), (0, 1, b, mul(eta, sig(a)))))
        sp = set(spread)
        assert len(sp) == q * q + 1 and sp <= set(lines)
        cover = sorted(p for L in spread for p in L)
        assert cover == list(range(n)), 'not a spread'
        self.spread = spread
        self.is_spread_line = [L in sp for L in lines]
        self.sp_of = [0] * n
        for k, L in enumerate(spread):
            for p in L:
                self.sp_of[p] = k


if __name__ == '__main__':
    W = W3F(int(sys.argv[1]), int(sys.argv[2]))
    print(len(W.pts), len(W.lines), len(W.spread))
