"""Small finite-field library for the referee checks of research/paper/joint.tex.
Elements of GF(p^e) are integers 0..q-1 (base-p digits = polynomial coefficients)."""

IRRED = {  # monic irreducible polynomials, coefficient list low->high (without leading 1)
    4: (2, [1, 1]),        # x^2 + x + 1
    8: (2, [1, 1, 0]),     # x^3 + x + 1
    9: (3, [1, 0]),        # x^2 + 1   (so i^2 = -1, as in the paper's F_9 = F_3[i])
    16: (2, [1, 1, 0, 0]), # x^4 + x + 1
    25: (5, [2, 0]),       # x^2 + 2  (-2=3 non-square mod 5)
    27: (3, [1, 2, 0]),    # x^3 + 2x + 1
}

class GF:
    def __init__(self, q):
        self.q = q
        p = q; e = 1
        for pp in range(2, q + 1):
            if q % pp == 0:
                p = pp; break
        e = 0; t = q
        while t > 1:
            assert t % p == 0
            t //= p; e += 1
        self.p, self.e = p, e
        if e == 1:
            self.add = [[(a + b) % p for b in range(q)] for a in range(q)]
            self.mul = [[(a * b) % p for b in range(q)] for a in range(q)]
        else:
            pr, low = IRRED[q]
            assert pr == p
            def tov(a):
                return [(a // p**i) % p for i in range(e)]
            def toi(v):
                return sum(c * p**i for i, c in enumerate(v))
            def pmul(a, b):
                va, vb = tov(a), tov(b)
                r = [0] * (2 * e - 1)
                for i in range(e):
                    for j in range(e):
                        r[i + j] = (r[i + j] + va[i] * vb[j]) % p
                for k in range(2 * e - 2, e - 1, -1):
                    c = r[k]
                    if c:
                        r[k] = 0
                        for i in range(e):
                            r[k - e + i] = (r[k - e + i] - c * low[i]) % p
                return toi(r[:e])
            self.add = [[toi([(x + y) % p for x, y in zip(tov(a), tov(b))]) for b in range(q)] for a in range(q)]
            self.mul = [[pmul(a, b) for b in range(q)] for a in range(q)]
        self.neg = [next(b for b in range(q) if self.add[a][b] == 0) for a in range(q)]
        self.inv = [None] + [next(b for b in range(1, q) if self.mul[a][b] == 1) for a in range(1, q)]
        self.sub = [[self.add[a][self.neg[b]] for b in range(q)] for a in range(q)]
        sq = set(self.mul[a][a] for a in range(1, q))
        self.squares = sq
        # check field axioms quickly
        for a in range(q):
            for b in range(q):
                assert self.mul[a][b] == self.mul[b][a]
        for a in range(1, q):
            assert self.mul[a][self.inv[a]] == 1
        # primitive element
        for g in range(2, q) if q > 2 else [1]:
            x, seen = 1, set()
            for _ in range(q - 1):
                x = self.mul[x][g]; seen.add(x)
            if len(seen) == q - 1:
                self.prim = g; break
    def chi(self, a):
        if a == 0: return 0
        return 1 if a in self.squares else -1
    def tr(self, a):  # absolute trace
        t, x = 0, a
        for _ in range(self.e):
            t = self.add[t][x]
            x = self.pw(x, self.p)
        return t
    def pw(self, a, n):
        r = 1
        for _ in range(n):
            r = self.mul[r][a]
        return r
    def elts(self):
        return range(self.q)
    def from_int(self, n):  # image of an integer
        n %= self.p
        r = 0
        for _ in range(n):
            r = self.add[r][1]
        return r
