"""Finite fields GF(q) for small prime powers, as lookup tables.  Elements are ints 0..q-1:
for q = p^e an element a_0 + a_1 x + ... is coded sum a_i p^i, reduced modulo a fixed irreducible polynomial.
GF(4) uses x^2 + x + 1, so the coding (a + b w -> a + 2b) matches research/theorems/graphs/build_d16D5_n33792.py."""
IRRED = {4: (1, 1, 1), 8: (1, 1, 0, 1), 9: (1, 0, 1), 16: (1, 1, 0, 0, 1), 25: (2, 1, 1), 27: (1, 2, 0, 1),
         32: (1, 0, 1, 0, 0, 1), 49: (3, 1, 1)}   # low-to-high coefficients, monic

def _factor(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e, r = 0, q
            while r % p == 0: r //= p; e += 1
            if r != 1: raise ValueError('not a prime power: %d' % q)
            return p, e

def _polymod(a, f, p):
    """remainder of a modulo monic f, coefficient lists low-to-high, over F_p"""
    a = a[:]
    while len(a) >= len(f):
        c = a[-1] % p
        if c:
            sh = len(a) - len(f)
            for t in range(len(f)): a[sh + t] = (a[sh + t] - c * f[t]) % p
        a.pop()
    while a and a[-1] % p == 0: a.pop()
    return a
def find_irreducible(p, e):
    """first monic irreducible polynomial of degree e over F_p (trial division by all monic polys of degree <= e/2)"""
    import itertools
    def monics(d): 
        for tail in itertools.product(range(p), repeat=d): yield list(tail) + [1]
    for f in monics(e):
        if f[0] == 0: continue
        if all(_polymod(f, g, p) for d in range(1, e // 2 + 1) for g in monics(d)): return tuple(f)
    raise ValueError('no irreducible polynomial')

class GF:
    def __init__(self, q):
        self.q = q; self.p, self.e = _factor(q); p, e = self.p, self.e
        digits = lambda a: [(a // p ** i) % p for i in range(e)]
        code = lambda d: sum(c * p ** i for i, c in enumerate(d))
        self.add = [[code([(x + y) % p for x, y in zip(digits(a), digits(b))]) for b in range(q)] for a in range(q)]
        self.neg = [code([(-x) % p for x in digits(a)]) for a in range(q)]
        if e == 1:
            self.mul = [[(a * b) % q for b in range(q)] for a in range(q)]
        else:
            f = IRRED[q] if q in IRRED else find_irreducible(p, e); assert len(f) == e + 1 and f[-1] == 1
            self.poly = f
            def pmul(da, db):
                r = [0] * (2 * e - 1)
                for i, x in enumerate(da):
                    for j, y in enumerate(db): r[i + j] = (r[i + j] + x * y) % p
                for d in range(2 * e - 2, e - 1, -1):          # reduce by the monic f
                    c = r[d]
                    if c:
                        for t in range(e + 1): r[d - e + t] = (r[d - e + t] - c * f[t]) % p
                return r[:e]
            self.mul = [[code(pmul(digits(a), digits(b))) for b in range(q)] for a in range(q)]
        self.sub = [[self.add[a][self.neg[b]] for b in range(q)] for a in range(q)]
        self.inv = [None] + [next(b for b in range(1, q) if self.mul[a][b] == 1) for a in range(1, q)]
        # sanity: field axioms on the tables
        for a in range(q):
            for b in range(q):
                assert self.mul[a][b] == self.mul[b][a] and self.add[a][b] == self.add[b][a]
        for a in range(1, q): assert self.mul[a][self.inv[a]] == 1
        mult = {1}; g = None
        for cand in (range(2, q) if q <= 512 else []):
            x, seen = cand, set()
            while x not in seen: seen.add(x); x = self.mul[x][cand]
            if len(seen) == q - 1: g = cand; break
        assert q == 2 or q > 512 or g is not None, 'no primitive element: bad irreducible polynomial'

    # vectors: tuples; matrices: tuples of row tuples
    def vadd(self, u, v): return tuple(self.add[a][b] for a, b in zip(u, v))
    def vscale(self, c, u): return tuple(self.mul[c][a] for a in u)
    def matvec(self, M, v):
        out = []
        for row in M:
            s = 0
            for a, b in zip(row, v): s = self.add[s][self.mul[a][b]]
            out.append(s)
        return tuple(out)
    def matmul(self, M, N):
        n = len(M); Nt = list(zip(*N))
        return tuple(tuple(self._dot(M[r], Nt[c]) for c in range(len(Nt))) for r in range(n))
    def _dot(self, u, v):
        s = 0
        for a, b in zip(u, v): s = self.add[s][self.mul[a][b]]
        return s
    def rank(self, vecs):
        rows = [list(v) for v in vecs]; r = 0; n = len(rows[0]) if rows else 0
        for c in range(n):
            piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            iv = self.inv[rows[r][c]]; rows[r] = [self.mul[iv][x] for x in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c]:
                    f = rows[i][c]; rows[i] = [self.sub[x][self.mul[f][y]] for x, y in zip(rows[i], rows[r])]
            r += 1
        return r
    def matinv(self, M):
        n = len(M); A = [list(M[r]) + [int(r == c) for c in range(n)] for r in range(n)]
        for c in range(n):
            piv = next((i for i in range(c, n) if A[i][c]), None)
            if piv is None: return None
            A[c], A[piv] = A[piv], A[c]
            iv = self.inv[A[c][c]]; A[c] = [self.mul[iv][x] for x in A[c]]
            for i in range(n):
                if i != c and A[i][c]:
                    f = A[i][c]; A[i] = [self.sub[x][self.mul[f][y]] for x, y in zip(A[i], A[c])]
        return tuple(tuple(row[n:]) for row in A)
    def span(self, vecs, n):
        """all vectors in the span (as a set of tuples)"""
        S = {tuple([0] * n)}
        for v in vecs:
            new = set()
            for s in S:
                for c in range(self.q): new.add(self.vadd(s, self.vscale(c, v)))
            S = new
        return S
    def canon(self, v):
        """projective representative: first nonzero coordinate 1 (None for the zero vector)"""
        for a in v:
            if a: return self.vscale(self.inv[a], v)
        return None

if __name__ == '__main__':
    for q in (2, 3, 4, 5, 7, 8, 9, 16):
        F = GF(q); print('GF(%d) ok, p=%d e=%d' % (q, F.p, F.e))
    F = GF(4); assert F.mul == [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]; print('GF(4) table matches build_d16D5_n33792.py')
