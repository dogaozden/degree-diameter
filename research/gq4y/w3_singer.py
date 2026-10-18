"""2-ovoids of W(3,q), q an odd prime, as unions of orbits of a cyclic group inside GF(q^4).

Model: PG(3,q) = GF(q^4)* / GF(q)*, the point g^i for i mod N = (q^4-1)/(q-1) (g primitive).
Symplectic form B(x,y) = Tr_{q^4/q}(delta * x * y^(q^2)) with delta^(q^2) = -delta: alternating, non-degenerate.
Multiplying by lam with lam^(q^2+1) in GF(q) scales B, so it maps W(3,q) to itself. These lam are g^k with
(q+1) | k, so the shift i -> i + (q+1) is a collineation of W(3,q); its orbits are the residue classes mod q+1
(size q^2+1). The shift by q^2-1 (lam^(q^2+1) = 1) is an isometry; orbits are classes mod 2(q+1).

Usage: python3 w3_singer.py q   (tests every union of 2 classes mod q+1, then 4 classes mod 2(q+1))
"""
import itertools
import sys

import numpy as np


class GF4:
    """GF(p^4) with log tables. Elements as 4-tuples (coefficients of 1, x, x^2, x^3)."""

    def __init__(self, p):
        self.p = p
        self.order = p ** 4 - 1
        # c = (c0, c1, c2, c3) with x^4 = -(c0 + c1 x + c2 x^2 + c3 x^3); build_exp indexes it reversed
        for c in itertools.product(range(p), repeat=4):
            if c[0] == 0:
                continue
            exp = self._exp(c)
            if exp is not None:
                break
        self.exp = exp
        self.log = {v: i for i, v in enumerate(exp)}

    def _exp(self, c):
        p, order = self.p, self.p ** 4 - 1
        v = (1, 0, 0, 0)
        exp = [v]
        for i in range(1, order + 1):
            top = v[3]
            v = ((-top * c[0]) % p, (v[0] - top * c[1]) % p, (v[1] - top * c[2]) % p, (v[2] - top * c[3]) % p)
            if v == (1, 0, 0, 0):
                return exp if i == order else None
            exp.append(v)
        return None

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def mul_log(self, i, j):
        return (i + j) % self.order

    def trace_of_log(self, i):
        """Tr(g^i) as an element of GF(p)."""
        q = self.p
        s = (0, 0, 0, 0)
        for k in range(4):
            s = self.add(s, self.exp[(i * q ** k) % self.order])
        assert s[1] == s[2] == s[3] == 0
        return s[0]


def w3(q):
    """Return (F, X, M, lines): point coordinates X (N x 4, X[i] = g^i), Gram matrix M of B, t.i. lines."""
    F = GF4(q)
    N = (q ** 4 - 1) // (q - 1)
    # delta with delta^(q^2) = -delta: delta = g^((q^2+1)/2) has delta^(q^2-1) = g^((q^4-1)/2) = -1
    dl = (q * q + 1) // 2
    # Gram on basis 1, g, g^2, g^3: M[a][b] = Tr(delta g^a g^(b q^2))
    M = np.array([[F.trace_of_log(dl + a + b * q * q) for b in range(4)] for a in range(4)], dtype=np.int64)
    assert ((M + M.T) % q == 0).all() and all(M[a][a] % q == 0 for a in range(4))
    assert round(np.linalg.det(M)) % q != 0
    X = np.array([F.exp[i] for i in range(N)], dtype=np.int64)
    G = (X @ M @ X.T) % q
    idx = {}
    for i in range(N):
        idx[normalize(X[i], q)] = i
    lines = set()
    for x in range(N):
        nb = set(np.nonzero(G[x] == 0)[0].tolist()) - {x}
        assert len(nb) == q * (q + 1)
        while nb:
            y = nb.pop()
            L = {x, y} | {idx[normalize(X[x] + a * X[y], q)] for a in range(1, q)}
            nb -= L
            lines.add(frozenset(L))
    lines = sorted(lines, key=sorted)
    assert len(lines) == (q + 1) * (q * q + 1)
    return F, X, M, lines


def normalize(v, p):
    v = [int(t) % p for t in v]
    for t in v:
        if t:
            inv = pow(t, p - 2, p)
            return tuple(u * inv % p for u in v)
    raise ValueError('zero vector')


def intersection_profile(S, lines):
    S = set(S)
    prof = {}
    for L in lines:
        k = len(L & S)
        prof[k] = prof.get(k, 0) + 1
    return prof


if __name__ == '__main__':
    q = int(sys.argv[1])
    F, X, M, lines = w3(q)
    N = len(X)
    print(f'W(3,{q}): {N} points, {len(lines)} lines')
    for m in (q + 1, 2 * (q + 1)):
        k = 2 if m == q + 1 else 4
        good = []
        for combo in itertools.combinations(range(m), k):
            S = [i for i in range(N) if i % m in combo]
            prof = intersection_profile(S, lines)
            if set(prof) == {2}:
                good.append(combo)
        print(f'classes mod {m}, unions of {k}: {len(good)} 2-ovoids', good[:10])
