#!/usr/bin/env python3
"""Finite groups as multiplication tables, for haar_search3.

Table file: a line with N, then N rows of N integers. Element 0 is the identity; entry [g][h] is g*h.

Usage: python3 groups.py [--check] NAME [NAME ...]
  Writes tables/NAME.txt next to this file. --check also runs check_table on each group.

Names:
  cyc_M                  cyclic group Z_M
  meta_M_K_L             Z_M x|_L Z_K; element (a, j) has index a*K + j (same indexing as haar_search2.c)
  heis_P                 3x3 upper unitriangular matrices over Z_P (order P^3, non-abelian)
  z2_P_K_diag_X_Y        Z_P^2 x| diag(X, Y), where diag(X, Y) has order exactly K
  z2_P_K_singer          Z_P^2 x| <gamma>, gamma in GF(P^2)^* of order exactly K (Singer cycle)
  agl_Q                  AGL(1,Q) = GF(Q) x| GF(Q)^*, Q a prime power
  aff_Q_K                GF(Q) x| C_K, C_K the subgroup of order K of GF(Q)^*
  sl_Q, psl_Q, pgl_Q     SL(2,Q), PSL(2,Q), PGL(2,Q)
  A__x__B                direct product of two named groups (index i*N_B + j)
"""
import itertools
import os
import random
import sys

TABLE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tables")


def from_mul(elements, mul, ident):
    """Table of a group given by its element list and multiplication. The identity goes to index 0."""
    elements = [ident] + [x for x in elements if x != ident]
    index = {x: i for i, x in enumerate(elements)}
    table = [[index[mul(x, y)] for y in elements] for x in elements]
    return table


def cyclic(m):
    return from_mul(range(m), lambda x, y: (x + y) % m, 0)


def meta(m, k, lam):
    """Z_m x|_lam Z_k, same product as haar_search2.c (requires lam^k = 1 mod m)."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError(f"lam^k != 1 mod m for m={m} k={k} lam={lam}")
    pw = [pow(lam, j, m) for j in range(k)]

    def mul(g, h):
        a, j = divmod(g, k)
        b, l = divmod(h, k)
        return ((a + pw[j] * b) % m) * k + (j + l) % k

    return from_mul(range(m * k), mul, 0)


def heis(p):
    """Upper unitriangular 3x3 matrices over Z_p: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    def mul(x, y):
        a, b, c = x
        a2, b2, c2 = y
        return ((a + a2) % p, (b + b2) % p, (c + c2 + a * b2) % p)

    return from_mul(itertools.product(range(p), repeat=3), mul, (0, 0, 0))


def factor_prime_power(q):
    for p in range(2, q + 1):
        if q % p == 0:
            e, r = 0, q
            while r % p == 0:
                r //= p
                e += 1
            if r != 1:
                break
            return p, e
    raise ValueError(f"{q} is not a prime power")


class GF:
    """GF(q) with elements 0..q-1 (base-p digits are the polynomial coefficients) and add/mul tables."""

    def __init__(self, q):
        self.q = q
        self.p, self.e = factor_prime_power(q)
        p, e = self.p, self.e
        if e == 1:
            self.add = [[(x + y) % p for y in range(q)] for x in range(q)]
            self.mul = [[(x * y) % p for y in range(q)] for x in range(q)]
        else:
            self._extension()
        self.neg = [next(y for y in range(q) if self.add[x][y] == 0) for x in range(q)]

    def _extension(self):
        p, e, q = self.p, self.e, self.q

        def digits(x):
            return [(x // p ** i) % p for i in range(e)]

        def undigits(ds):
            return sum(d * p ** i for i, d in enumerate(ds))

        self.add = [[undigits([(u + v) % p for u, v in zip(digits(x), digits(y))]) for y in range(q)]
                    for x in range(q)]
        # Try monic irreducibles x^e + c_{e-1} x^{e-1} + ... + c_0 until there are no zero divisors.
        for c in itertools.product(range(p), repeat=e):
            def pmul(a, b, c=c):
                prod = [0] * (2 * e - 1)
                for i, x in enumerate(a):
                    for j, y in enumerate(b):
                        prod[i + j] = (prod[i + j] + x * y) % p
                for deg in range(2 * e - 2, e - 1, -1):
                    coef = prod[deg]
                    if coef:
                        prod[deg] = 0
                        for i in range(e):
                            prod[deg - e + i] = (prod[deg - e + i] - coef * c[i]) % p
                return prod[:e]

            mul = [[undigits(pmul(digits(x), digits(y))) for y in range(q)] for x in range(q)]
            if all(mul[x][y] for x in range(1, q) for y in range(1, q)):
                self.mul = mul
                return
        raise RuntimeError(f"no irreducible polynomial found for q={q}")

    def power(self, x, n):
        r = 1
        for _ in range(n):
            r = self.mul[r][x]
        return r


def affine(q, k):
    """GF(q) x| C_k with C_k = {x in GF(q)^* : x^k = 1}; the element (b, a) is the map t -> a*t + b."""
    F = GF(q)
    H = [a for a in range(1, q) if F.power(a, k) == 1]
    if len(H) != k:
        raise ValueError(f"k={k} does not divide q-1={q - 1}")
    elements = [(b, a) for b in range(q) for a in H]

    def mul(g, h):
        (b1, a1), (b2, a2) = g, h
        return (F.add[F.mul[a1][b2]][b1], F.mul[a1][a2])

    return from_mul(elements, mul, (0, 1))


def matrix_group(kind, q):
    """SL(2,q), PSL(2,q) or PGL(2,q). Elements of the quotients are represented by canonical 2x2 tuples."""
    F = GF(q)

    def mul_m(x, y):
        a, b, c, d = x
        a2, b2, c2, d2 = y
        A, M, N = F.add, F.mul, F.neg
        return (A[M[a][a2]][M[b][c2]], A[M[a][b2]][M[b][d2]],
                A[M[c][a2]][M[d][c2]], A[M[c][b2]][M[d][d2]])

    def det(x):
        a, b, c, d = x
        return F.add[F.mul[a][d]][F.neg[F.mul[b][c]]]

    if kind == "sl":
        def canon(x):
            return x
        mats = [m for m in itertools.product(range(q), repeat=4) if det(m) == 1]
    elif kind == "psl":
        def canon(x):
            return min(x, tuple(F.neg[v] for v in x))
        mats = [m for m in itertools.product(range(q), repeat=4) if det(m) == 1]
    else:  # pgl
        def canon(x):
            return min(tuple(F.mul[c][v] for v in x) for c in range(1, q))
        mats = [m for m in itertools.product(range(q), repeat=4) if det(m) != 0]

    ident = canon((1, 0, 0, 1))
    elements = sorted({canon(m) for m in mats})
    return from_mul(elements, lambda x, y: canon(mul_m(x, y)), ident)


def z2_semidirect(p, k, A):
    """Z_p^2 x| <A> with A (2x2 over Z_p, given as (a11, a12, a21, a22)) of order k."""
    def matmul(X, Y):
        a, b, c, d = X
        e, f, g, h = Y
        return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)

    Apow = [(1, 0, 0, 1)]
    for _ in range(k - 1):
        Apow.append(matmul(Apow[-1], A))
    if matmul(Apow[-1], A) != (1, 0, 0, 1) or any(M == (1, 0, 0, 1) for M in Apow[1:]):
        raise ValueError(f"matrix {A} does not have order exactly {k} mod {p}")

    def mul(g, h):
        (x, y, j), (u, v, l) = g, h
        M = Apow[j]
        return ((x + M[0] * u + M[1] * v) % p, (y + M[2] * u + M[3] * v) % p, (j + l) % k)

    elements = [(x, y, j) for x in range(p) for y in range(p) for j in range(k)]
    return from_mul(elements, mul, (0, 0, 0))


def z2_diag(p, k, X, Y):
    return z2_semidirect(p, k, (X % p, 0, 0, Y % p))


def z2_singer(p, k):
    """Multiplication by gamma on GF(p^2) = Z_p^2, with gamma of order exactly k."""
    F = GF(p * p)
    for gamma in range(1, p * p):
        if F.power(gamma, k) == 1 and all(F.power(gamma, j) != 1 for j in range(1, k)):
            # Columns: image of 1 is gamma, image of t (the element p, digits (0,1)) is gamma*t.
            col0 = (gamma % p, gamma // p)
            gt = F.mul[gamma][p]
            col1 = (gt % p, gt // p)
            return z2_semidirect(p, k, (col0[0], col1[0], col0[1], col1[1]))
    raise ValueError(f"GF({p * p})^* has no element of order {k}")


def product(T1, T2):
    N1, N2 = len(T1), len(T2)
    rows = []
    for x in range(N1 * N2):
        i1, j1 = divmod(x, N2)
        r1, r2 = T1[i1], T2[j1]
        rows.append([T1[i1][i2] * N2 + T2[j1][j2] for i2 in range(N1) for j2 in range(N2)])
    return rows


def build(name):
    if "__x__" in name:
        a, b = name.split("__x__")
        return product(build(a), build(b))
    f = name.split("_")
    kind = f[0]
    if kind == "cyc":
        return cyclic(int(f[1]))
    if kind == "meta":
        return meta(int(f[1]), int(f[2]), int(f[3]))
    if kind == "heis":
        return heis(int(f[1]))
    if kind == "z2" and f[3] == "diag":
        return z2_diag(int(f[1]), int(f[2]), int(f[4]), int(f[5]))
    if kind == "z2" and f[3] == "singer":
        return z2_singer(int(f[1]), int(f[2]))
    if kind == "agl":
        return affine(int(f[1]), int(f[1]) - 1)
    if kind == "aff":
        return affine(int(f[1]), int(f[2]))
    if kind in ("sl", "psl", "pgl"):
        return matrix_group(kind, int(f[1]))
    raise ValueError(f"unknown group name {name}")


def check_table(table, trials=100000, seed=1):
    """Identity, row/column cancellation, inverses, associativity on random triples. Raises AssertionError."""
    N = len(table)
    assert all(len(r) == N for r in table), "not square"
    assert all(v in range(N) for r in table for v in r), "entry out of range (closure)"
    assert all(table[0][h] == h and table[h][0] == h for h in range(N)), "identity"
    full = list(range(N))
    for g in range(N):
        assert sorted(table[g]) == full, f"row {g} is not a permutation"
        assert any(table[g][h] == 0 for h in range(N)), f"no inverse for {g}"
    rng = random.Random(seed)
    for _ in range(trials):
        a, b, c = rng.randrange(N), rng.randrange(N), rng.randrange(N)
        assert table[table[a][b]][c] == table[a][table[b][c]], f"associativity fails at {a},{b},{c}"
    return N


def write_table(path, table):
    with open(path, "w") as f:
        f.write(f"{len(table)}\n")
        for row in table:
            f.write(" ".join(map(str, row)) + "\n")


def main(argv):
    check = "--check" in argv
    names = [a for a in argv if a != "--check"]
    if not names:
        print(__doc__)
        return 1
    os.makedirs(TABLE_DIR, exist_ok=True)
    for name in names:
        table = build(name)
        N = len(table)
        if check:
            check_table(table)
        path = os.path.join(TABLE_DIR, name + ".txt")
        write_table(path, table)
        print(f"{name} N={N} {'checked ' if check else ''}-> {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
