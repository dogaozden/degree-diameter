"""Small exact group arithmetic for the BEYOND_RANDOM.md experiments: Q x Z_n with Q = SL(2,q) or PSL(2,q), q = p^e,
and the automorphisms the structured search uses (conjugation, Frobenius on the entries, z -> r z on Z_n).
Elements are tuples (a, b, c, d, z) with field elements encoded as ints 0..q-1. PSL elements are stored in a normal
form (first nonzero of (a, b) taken from the 'lower half' of the field) so that equality is tuple equality."""
import itertools, random

class GF:
    """GF(p^e) by tables. Elements are ints; for e > 1 the polynomial basis of a fixed irreducible."""
    IRR = {(2, 3): (1, 1, 0, 1), (2, 2): (1, 1, 1), (3, 2): (1, 0, 1), (3, 3): (1, 2, 0, 1), (2, 6): (1, 1, 0, 0, 0, 0, 1),
           (5, 2): (2, 0, 1), (7, 2): (1, 0, 1), (2, 4): (1, 1, 0, 0, 1), (5, 3): (3, 3, 0, 1)}   # c0 + c1 X + ... (monic)

    def __init__(self, p, e=1):
        self.p, self.e, self.q = p, e, p ** e
        q = self.q
        if e == 1:
            self.add = [[(x + y) % p for y in range(q)] for x in range(q)]
            self.mul = [[(x * y) % p for y in range(q)] for x in range(q)]
        else:
            irr = self.IRR[(p, e)]
            dig = lambda x: [(x // p ** i) % p for i in range(e)]
            enc = lambda v: sum(c * p ** i for i, c in enumerate(v))
            self.add = [[enc([(a + b) % p for a, b in zip(dig(x), dig(y))]) for y in range(q)] for x in range(q)]
            def pm(x, y):
                a, b = dig(x), dig(y); r = [0] * (2 * e - 1)
                for i in range(e):
                    for j in range(e): r[i + j] = (r[i + j] + a[i] * b[j]) % p
                for k in range(2 * e - 2, e - 1, -1):          # reduce X^k = -(c0 + ... + c_{e-1} X^{e-1}) X^{k-e}
                    c = r[k]
                    if c:
                        r[k] = 0
                        for i in range(e): r[k - e + i] = (r[k - e + i] - c * irr[i]) % p
                return enc(r[:e])
            self.mul = [[pm(x, y) for y in range(q)] for x in range(q)]
        self.neg = [next(y for y in range(q) if self.add[x][y] == 0) for x in range(q)]
        self.inv = [0] + [next(y for y in range(q) if self.mul[x][y] == 1) for x in range(1, q)]
        self.frob = [self.pw(x, p) for x in range(q)]
        # PSL normal form: pick, for each pair {u, -u}, the smaller int as representative
        self.half = [min(x, self.neg[x]) == x for x in range(q)]

    def pw(self, x, k):
        r = 1
        for _ in range(k): r = self.mul[r][x]
        return r


class QxZ:
    """SL(2,q) or PSL(2,q) times Z_n."""

    def __init__(self, fam, p, e=1, n=1):
        self.F = F = GF(p, e); self.fam, self.n, self.q = fam, n, F.q
        self.psl = fam == 'psl' and p != 2
        self.elems_Q = None

    def norm(self, a, b, c, d):
        if not self.psl: return (a, b, c, d)
        F = self.F; lead = a if a else b
        if F.half[lead]: return (a, b, c, d)
        return (F.neg[a], F.neg[b], F.neg[c], F.neg[d])

    def mul(self, x, y):
        F = self.F; A, M = F.add, F.mul
        a = A[M[x[0]][y[0]]][M[x[1]][y[2]]]; b = A[M[x[0]][y[1]]][M[x[1]][y[3]]]
        c = A[M[x[2]][y[0]]][M[x[3]][y[2]]]; d = A[M[x[2]][y[1]]][M[x[3]][y[3]]]
        return self.norm(a, b, c, d) + ((x[4] + y[4]) % self.n,)

    def inv(self, x):
        F = self.F
        return self.norm(x[3], F.neg[x[1]], F.neg[x[2]], x[0]) + ((-x[4]) % self.n,)

    def e(self): return (1, 0, 0, 1, 0)

    def order(self):
        q = self.q; o = q * (q * q - 1)
        return (o // 2 if self.psl else o) * self.n

    def rand(self, rng):
        F = self.F; q = self.q
        while True:
            a, b, c = rng.randrange(q), rng.randrange(q), rng.randrange(q)
            if a:
                d = F.mul[F.add[1][F.mul[b][c]]][F.inv[a]]          # ad - bc = 1
            else:
                if not b or not c: continue
                if F.mul[b][c] != F.neg[1]: continue
                d = rng.randrange(q)
            if F.add[F.mul[a][d]][F.neg[F.mul[b][c]]] != 1: continue
            return self.norm(a, b, c, d) + (rng.randrange(self.n),)

    def all_Q(self):
        if self.elems_Q is None:
            F = self.F; q = self.q; s = set()
            for a, b, c, d in itertools.product(range(q), repeat=4):
                if F.add[F.mul[a][d]][F.neg[F.mul[b][c]]] == 1: s.add(self.norm(a, b, c, d))
            self.elems_Q = sorted(s)
        return self.elems_Q

    def order_of(self, x):
        y, k = x, 1
        while y != self.e():
            y = self.mul(y, x); k += 1
        return k


def unit_order3(n):
    """r with r^3 = 1 mod n and the fewest fixed z (gcd(r - 1, n)); 1 if none."""
    best = (n + 1, 1)
    for r in range(2, n):
        if pow(r, 3, n) == 1 % n:
            from math import gcd
            best = min(best, (gcd(r - 1, n), r))
    return best[1] if n > 1 else 0


class Conj:
    """alpha(x) = g x g^-1 on Q, z -> r z on Z_n."""
    def __init__(self, G, g, r):
        self.G, self.g, self.gi, self.r = G, g, G.inv(g), r
    def __call__(self, x):
        G = self.G; y = G.mul(G.mul(self.g, x[:4] + (0,)), self.gi)
        return y[:4] + ((self.r * x[4]) % G.n,)


class Frob:
    """alpha(x) = x^(p^j) entrywise on Q, z -> r z on Z_n."""
    def __init__(self, G, j, r):
        self.G, self.j, self.r = G, j, r
    def __call__(self, x):
        G = self.G; F = G.F; y = list(x[:4])
        for _ in range(self.j): y = [F.frob[t] for t in y]
        return G.norm(*y) + ((self.r * x[4]) % G.n,)


def find_order3_conj(G, rng, want_trace=None):
    """an element g of Q whose conjugation has order 3 (g of order 3, or 6 with g^3 central)."""
    while True:
        g = G.rand(rng)[:4] + (0,)
        g3 = G.mul(G.mul(g, g), g)
        if g == G.e(): continue
        central = g3 == G.e() or g3 == G.norm(G.F.neg[1], 0, 0, G.F.neg[1]) + (0,)
        g1 = g; is_scalar = g1[1] == 0 and g1[2] == 0 and g1[0] == g1[3]
        if central and not is_scalar: return g


def fixed_points(G, alpha):
    out = []
    for xq in G.all_Q():
        for z in range(G.n):
            x = xq + (z,)
            if alpha(x) == x: out.append(x)
    return out
