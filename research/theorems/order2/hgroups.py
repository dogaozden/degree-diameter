"""Small exact group library for the ORDER2 analysis: G = Q x Z_n, Q = SL(2,q) or PSL(2,q), q a prime power,
or a direct product of two such matrix groups.  Elements are indexed 0..N-1 (index = qindex * n + z).  Every
group operation is a numpy permutation array, so word values for whole generator sets are cheap.

Field encoding matches research/frontier/haar_gen3.c (and haar_sym/haar_inv): GF(p^k) = GF(p)[x]/(f), f the first
monic irreducible polynomial with f(0) != 0 in the order of its coefficient code, elements written as sum c_i p^i.
So the mat(a,b,c,d) and z= fields of a haar_gen3 solution file can be read directly.
"""
import numpy as np


def _poly_irreducible(f, k, p):
    # f: coefficients low->high, monic of degree k; brute force over monic g of degree 1..k/2
    for dg in range(1, k // 2 + 1):
        for code in range(p ** dg):
            g = [(code // p ** i) % p for i in range(dg)] + [1]
            r = list(f)
            for i in range(k, dg - 1, -1):
                t = r[i]
                if t:
                    for j in range(dg + 1):
                        r[i - dg + j] = (r[i - dg + j] - t * g[j]) % p
            if not any(r):
                return False
    return True


class Field:
    def __init__(self, q):
        p = next(t for t in range(2, q + 1) if q % t == 0)
        k, x = 0, q
        while x % p == 0:
            x //= p
            k += 1
        assert x == 1, f"{q} is not a prime power"
        self.q, self.p, self.k = q, p, k
        if k == 1:
            poly = [0, 1]
        else:
            poly = None
            for code in range(p ** k):
                f = [(code // p ** i) % p for i in range(k)] + [1]
                if f[0] and _poly_irreducible(f, k, p):
                    poly = f
                    break
        self.poly = poly
        dig = np.array([[(a // p ** i) % p for i in range(k)] for a in range(q)], dtype=np.int64)
        pw = np.array([p ** i for i in range(k)], dtype=np.int64)
        self.add = ((dig[:, None, :] + dig[None, :, :]) % p) @ pw
        mul = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            for b in range(q):
                pr = [0] * (2 * k)
                for i in range(k):
                    for j in range(k):
                        pr[i + j] = (pr[i + j] + dig[a, i] * dig[b, j]) % p
                for i in range(2 * k - 2, k - 1, -1):
                    t = pr[i]
                    if t:
                        for j in range(k + 1):
                            pr[i - k + j] = (pr[i - k + j] - t * poly[j]) % p
                mul[a, b] = sum(pr[i] * p ** i for i in range(k))
        self.mul = mul
        self.neg = np.array([int(np.where(self.add[a] == 0)[0][0]) for a in range(q)])
        self.inv = np.zeros(q, dtype=np.int64)
        for a in range(1, q):
            self.inv[a] = int(np.where(mul[a] == 1)[0][0])

    def poly_str(self):
        terms = []
        for i in range(self.k, -1, -1):
            c = self.poly[i]
            if not c:
                continue
            if i == 0:
                terms.append(str(c))
            else:
                terms.append(("" if c == 1 else str(c)) + ("x" if i == 1 else f"x^{i}"))
        return "+".join(terms)


class MatGroup:
    """SL(2,q) or PSL(2,q). Elements stored as int arrays a,b,c,d (canonical representative for PSL)."""

    def __init__(self, kind, q):
        self.kind, self.q = kind, q
        F = self.F = Field(q)
        if kind == "psl" and F.p == 2:
            kind = self.kind = "sl"
        a, b, c = np.meshgrid(np.arange(q), np.arange(q), np.arange(q), indexing="ij")
        a, b, c = a.ravel(), b.ravel(), c.ravel()
        # a != 0: d = (1 + b c) / a
        m = a != 0
        A1, B1, C1 = a[m], b[m], c[m]
        D1 = F.mul[F.inv[A1], F.add[1, F.mul[B1, C1]]]
        # a == 0: b != 0, c = -1/b, d free
        bb, dd = np.meshgrid(np.arange(1, q), np.arange(q), indexing="ij")
        bb, dd = bb.ravel(), dd.ravel()
        A2, B2, C2, D2 = np.zeros_like(bb), bb, F.neg[F.inv[bb]], dd
        A = np.concatenate([A1, A2]); B = np.concatenate([B1, B2]); C = np.concatenate([C1, C2]); D = np.concatenate([D1, D2])
        if kind == "psl":
            k1 = self._key(A, B, C, D)
            k2 = self._key(F.neg[A], F.neg[B], F.neg[C], F.neg[D])
            keep = k1 <= k2
            A, B, C, D = A[keep], B[keep], C[keep], D[keep]
        key = self._key(A, B, C, D)
        o = np.argsort(key)
        self.A, self.B, self.C, self.D, self.keys = A[o], B[o], C[o], D[o], key[o]
        self.order = len(self.keys)
        self.ident = self.index(np.array([1]), np.array([0]), np.array([0]), np.array([1]))[0]
        self.spec = f"{kind} {q}" + ("" if F.k == 1 else f" poly {F.poly_str()}")

    def _key(self, a, b, c, d):
        q = self.q
        return ((a.astype(np.int64) * q + b) * q + c) * q + d

    def index(self, a, b, c, d):
        F = self.F
        k = self._key(a, b, c, d)
        if self.kind == "psl":
            k = np.minimum(k, self._key(F.neg[a], F.neg[b], F.neg[c], F.neg[d]))
        i = np.searchsorted(self.keys, k)
        assert np.all(self.keys[np.minimum(i, self.order - 1)] == k), "not a group element"
        return i

    def mul_vec(self, x, y):
        """x*y for index arrays (broadcast)."""
        F = self.F
        a1, b1, c1, d1 = self.A[x], self.B[x], self.C[x], self.D[x]
        a2, b2, c2, d2 = self.A[y], self.B[y], self.C[y], self.D[y]
        a = F.add[F.mul[a1, a2], F.mul[b1, c2]]
        b = F.add[F.mul[a1, b2], F.mul[b1, d2]]
        c = F.add[F.mul[c1, a2], F.mul[d1, c2]]
        d = F.add[F.mul[c1, b2], F.mul[d1, d2]]
        return self.index(a, b, c, d)

    def inv_vec(self, x):
        F = self.F
        return self.index(self.D[x], F.neg[self.B[x]], F.neg[self.C[x]], self.A[x])

    def trace(self, x):
        return self.F.add[self.A[x], self.D[x]]

    def desc(self, x):
        return f"mat({self.A[x]},{self.B[x]},{self.C[x]},{self.D[x]})"

    def find(self, a, b, c, d):
        return int(self.index(np.array([a]), np.array([b]), np.array([c]), np.array([d]))[0])

    def frob_vec(self, x, j):
        """entrywise x -> x^(p^j)"""
        F = self.F
        e = F.p ** j
        fr = np.zeros(F.q, dtype=np.int64)
        for t in range(F.q):
            y = 1
            for _ in range(e):
                y = F.mul[y, t]
            fr[t] = y if t else 0
        return self.index(fr[self.A[x]], fr[self.B[x]], fr[self.C[x]], fr[self.D[x]])


class ProdGroup:
    def __init__(self, g1, g2):
        self.g1, self.g2 = g1, g2
        self.order = g1.order * g2.order
        self.ident = g1.ident * g2.order + g2.ident
        self.spec = f"prod {g1.spec} {g2.spec}"

    def mul_vec(self, x, y):
        o2 = self.g2.order
        return self.g1.mul_vec(x // o2, y // o2) * o2 + self.g2.mul_vec(x % o2, y % o2)

    def inv_vec(self, x):
        o2 = self.g2.order
        return self.g1.inv_vec(x // o2) * o2 + self.g2.inv_vec(x % o2)

    def desc(self, x):
        o2 = self.g2.order
        return f"prod[{self.g1.desc(x // o2)};{self.g2.desc(x % o2)}]"


class Group:
    """G = Q x Z_n.  Index = qindex * n + z."""

    def __init__(self, Q, n):
        self.Q, self.n = Q, n
        self.N = Q.order * n
        self.ident = int(Q.ident) * n
        self.spec = f"{Q.spec} x Z_{n}"
        self._inv = None

    def mul_vec(self, x, y):
        n = self.n
        return self.Q.mul_vec(x // n, y // n) * n + (x % n + y % n) % n

    def left_perm(self, s):
        """L[g] = s*g for all g."""
        allg = np.arange(self.N)
        return self.mul_vec(np.full(self.N, s), allg)

    def inv_perm(self):
        if self._inv is None:
            allg = np.arange(self.N)
            n = self.n
            self._inv = self.Q.inv_vec(allg // n) * n + (-(allg % n)) % n
        return self._inv

    def elem(self, qidx, z):
        return qidx * self.n + (z % self.n)


def parse_group(tokens):
    """tokens like ['psl','11'] or ['sl','25'] or ['prod','sl','5','psl','7']; returns (Q, rest)."""
    t = tokens[0]
    if t in ("sl", "psl"):
        q = int(tokens[1])
        rest = tokens[2:]
        if rest[:1] == ["poly"]:
            rest = rest[2:]
        return MatGroup(t, q), rest
    if t == "prod":
        g1, r1 = parse_group(tokens[1:])
        g2, r2 = parse_group(r1)
        return ProdGroup(g1, g2), r2
    raise ValueError(t)


def read_solution(path):
    """haar_gen3-format solution file -> (d, D, Group, list of element indices)."""
    import re
    lines = open(path).read().split("\n")
    head = lines[0].split()
    d, D = int(head[0]), int(head[1])
    toks = head[2:]
    Q, rest = parse_group(toks)
    n = int(rest[rest.index("n") + 1])
    G = Group(Q, n)
    S = []
    for ln in lines[1:1 + d]:
        mats = re.findall(r"mat\((\d+),(\d+),(\d+),(\d+)\)", ln)
        z = int(re.search(r"z=(-?\d+)", ln).group(1))
        if isinstance(Q, MatGroup):
            (a, b, c, dd), = mats
            qi = Q.find(int(a), int(b), int(c), int(dd))
        else:
            (a1, b1, c1, d1), (a2, b2, c2, d2) = mats
            qi = Q.g1.find(int(a1), int(b1), int(c1), int(d1)) * Q.g2.order + Q.g2.find(int(a2), int(b2), int(c2), int(d2))
        S.append(G.elem(qi, z))
    return d, D, G, S
