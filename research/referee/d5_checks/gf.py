"""Small finite fields GF(p^k) for the referee checks (written for this report; shares no code with d5gq/).
Elements are integers 0..q-1: e = c0 + c1 p + ... + c_{k-1} p^{k-1}, coefficients of a polynomial in x
modulo a monic irreducible polynomial f of degree k (given by its coefficient list, low degree first)."""
import itertools

def _irreducibles(p, k):
    # monic polynomials of degree k with no root and (for k<=3) hence irreducible; k<=3 suffices here
    out = []
    for low in itertools.product(range(p), repeat=k):
        f = list(low) + [1]
        if k <= 3 and all(sum(c * pow(t, i, p) for i, c in enumerate(f)) % p for t in range(p)):
            out.append(f)
    return out

class GF:
    def __init__(self, q, f=None):
        p = next(d for d in range(2, q + 1) if q % d == 0)
        k = 0; t = q
        while t > 1:
            assert t % p == 0; t //= p; k += 1
        self.p, self.k, self.q = p, k, q
        if k == 1:
            f = [0, 1]
        elif f is None:
            f = _irreducibles(p, k)[0]
        self.f = f
        self.add = [[self._add(a, b) for b in range(q)] for a in range(q)]
        self.mul = [[self._mul(a, b) for b in range(q)] for a in range(q)]
        self.neg = [next(b for b in range(q) if self.add[a][b] == 0) for a in range(q)]
        self.inv = [None] + [next(b for b in range(q) if self.mul[a][b] == 1) for a in range(1, q)]
        self.sub = [[self.add[a][self.neg[b]] for b in range(q)] for a in range(q)]
        # sanity: field axioms on the tables
        for a in range(q):
            for b in range(q):
                assert self.mul[a][b] == self.mul[b][a]
        assert all(self.inv[a] is not None for a in range(1, q))

    def _vec(self, a):
        return [(a // self.p ** i) % self.p for i in range(self.k)]

    def _int(self, v):
        return sum(c * self.p ** i for i, c in enumerate(v))

    def _add(self, a, b):
        return self._int([(x + y) % self.p for x, y in zip(self._vec(a), self._vec(b))])

    def _mul(self, a, b):
        p, k = self.p, self.k
        if k == 1:
            return a * b % p
        va, vb = self._vec(a), self._vec(b)
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(va):
            for j, y in enumerate(vb):
                prod[i + j] = (prod[i + j] + x * y) % p
        for d in range(2 * k - 2, k - 1, -1):  # reduce x^d = -(f_0 + ... + f_{k-1} x^{k-1}) x^{d-k}
            c = prod[d]
            if c:
                prod[d] = 0
                for i in range(k):
                    prod[d - k + i] = (prod[d - k + i] - c * self.f[i]) % p
        return self._int(prod[:k])

    def irreducible_quadratic(self):
        """(alpha, beta) with X^2 - beta X - alpha irreducible."""
        for al in range(self.q):
            for be in range(self.q):
                if all(self.sub[self.sub[self.mul[t][t]][self.mul[be][t]]][al] != 0 for t in range(self.q)):
                    return al, be

def normalize(F, v):
    """projective normal form: first non-zero coordinate 1"""
    for c in v:
        if c:
            ic = F.inv[c]
            return tuple(F.mul[ic][x] for x in v)
    raise ValueError("zero vector")

def proj_points(F, n):
    """points of PG(n-1, q) as normalized n-tuples"""
    pts = []
    for v in itertools.product(range(F.q), repeat=n):
        if any(v) and normalize(F, v) == v:
            pts.append(v)
    return pts

def span_points(F, x, y):
    """the q+1 points of the projective line <x, y>"""
    out = {normalize(F, x)}
    for c in range(F.q):
        out.add(normalize(F, tuple(F.add[F.mul[c][a]][b] for a, b in zip(x, y))))
    return out
