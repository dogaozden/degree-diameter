"""Small finite fields GF(q), q <= 16, as addition/multiplication tables (table-audit).
q prime: integers mod q. q = p^e: polynomials mod 4: x^2+x+1, 8: x^3+x+1, 9: x^2+1, 16: x^4+x+1 (the same choice as
moore_build.c); element index = coefficient vector in base p."""

RED = {4: [1, 1], 8: [1, 1, 0], 9: [2, 0], 16: [1, 1, 0, 0]}   # x^e = sum RED[i] x^i


class GF:
    def __init__(self, q):
        p = next(t for t in range(2, q + 1) if q % t == 0)
        e, r = 1, p
        while r < q:
            r *= p
            e += 1
        assert r == q
        self.q, self.p, self.e = q, p, e
        red = RED.get(q, [0])
        vec = lambda a: [(a // p ** i) % p for i in range(e)]
        num = lambda c: sum(c[i] * p ** i for i in range(e))
        self.add = [[num([(x + y) % p for x, y in zip(vec(a), vec(b))]) for b in range(q)] for a in range(q)]
        mul = []
        for a in range(q):
            row = []
            for b in range(q):
                ca, cb = vec(a), vec(b)
                pr = [0] * (2 * e)
                for i in range(e):
                    for j in range(e):
                        pr[i + j] = (pr[i + j] + ca[i] * cb[j]) % p
                for k in range(2 * e - 2, e - 1, -1):
                    c, pr[k] = pr[k], 0
                    for i in range(e):
                        pr[k - e + i] = (pr[k - e + i] + c * red[i]) % p
                row.append(num(pr[:e]))
            mul.append(row)
        self.mul = mul
        self.neg = [next(b for b in range(q) if self.add[a][b] == 0) for a in range(q)]
        self.inv = [None] + [next(b for b in range(q) if mul[a][b] == 1) for a in range(1, q)]
        for a in range(1, q):
            assert mul[a][self.inv[a]] == 1

    def sub(self, a, b):
        return self.add[a][self.neg[b]]

    def dot(self, x, y):
        s = 0
        for a, b in zip(x, y):
            s = self.add[s][self.mul[a][b]]
        return s

    def normalize(self, v):
        for a in v:
            if a:
                s = self.inv[a]
                return tuple(self.mul[s][c] for c in v)
        return tuple(v)

    def irreducible_quadratic(self):
        """(a, b) with T^2 - aT + b^2 irreducible over GF(q), b != 0."""
        for a in range(self.q):
            for b in range(1, self.q):
                bb = self.mul[b][b]
                if all(self.add[self.sub(self.mul[t][t], self.mul[a][t])][bb] != 0 for t in range(self.q)):
                    return a, b
        raise ValueError
