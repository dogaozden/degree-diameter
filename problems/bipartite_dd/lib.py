"""Helper library for graph-construction programs (import as `import lib`).

Graphs are given as `(n, edges)`: `n` vertices labelled 0..n-1 and `edges`, a list of
`(u, v)` pairs. Edges are undirected. Uses only the standard library and numpy.
"""
import itertools

import numpy as np


# ---------------------------------------------------------------- finite fields

def _prime_power(q):
    """Return (p, k) if q == p**k for a prime p and k >= 1, else None."""
    if q < 2:
        return None
    p = next(d for d in range(2, q + 1) if q % d == 0)  # smallest prime factor
    k = 0
    while q % p == 0:
        q //= p
        k += 1
    return (p, k) if q == 1 else None


def is_prime_power(q):
    """Return True if q is a prime power p**k with k >= 1."""
    return _prime_power(q) is not None


def _poly_rem(a, f, p):
    """Remainder of polynomial a modulo monic polynomial f over Z_p (lists, lowest degree first)."""
    a = list(a)
    d = len(f) - 1
    for i in range(len(a) - 1, d - 1, -1):
        c = a[i]
        if c:
            for j in range(d + 1):
                a[i - d + j] = (a[i - d + j] - c * f[j]) % p
    return a[:d]


def _is_irreducible(f, p):
    """True if monic polynomial f (lowest degree first) has no monic factor of degree 1..deg/2 over Z_p."""
    k = len(f) - 1
    for d in range(1, k // 2 + 1):
        for low in itertools.product(range(p), repeat=d):
            g = list(low) + [1]  # monic of degree d
            if not any(_poly_rem(f, g, p)):
                return False
    return True


class GF:
    """Finite field of prime-power order q. Elements are ints 0..q-1 (base-p digits = polynomial coefficients)."""

    def __init__(self, q):
        """Build GF(q) with add/mul tables; raise ValueError if q is not a prime power."""
        pk = _prime_power(q)
        if pk is None:
            raise ValueError(f"{q} is not a prime power")
        self.q = q
        self.p, self.k = pk
        p, k = pk
        # Modulus: the lexicographically first monic irreducible of degree k (x for k = 1).
        if k == 1:
            self._modulus = [0, 1]
        else:
            for top_down in itertools.product(range(p), repeat=k):
                f = list(reversed(top_down)) + [1]
                if _is_irreducible(f, p):
                    self._modulus = f
                    break
        # Addition is digit-wise mod p.
        els = np.arange(q, dtype=np.int64)
        digits = [(els // p**i) % p for i in range(k)]
        self.add_table = sum(((da[:, None] + da[None, :]) % p) * p**i for i, da in enumerate(digits))
        self._neg = sum(((-da) % p) * p**i for i, da in enumerate(digits))
        # Multiplication: find a generator g, then use log/exp tables.
        g, powers = self._find_generator()
        self._primitive = g
        exp = np.array(powers, dtype=np.int64)  # exp[i] = g**i, i = 0..q-2
        log = np.zeros(q, dtype=np.int64)
        log[exp] = np.arange(q - 1)
        self._exp, self._log = exp, log
        self.mul_table = np.zeros((q, q), dtype=np.int64)
        self.mul_table[1:, 1:] = exp[(log[1:, None] + log[None, 1:]) % (q - 1)]

    def _poly_mul(self, a, b):
        """Multiply two field elements by polynomial arithmetic (used only to build the tables)."""
        p, k = self.p, self.k
        da = [(a // p**i) % p for i in range(k)]
        db = [(b // p**i) % p for i in range(k)]
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(da):
            for j, y in enumerate(db):
                prod[i + j] = (prod[i + j] + x * y) % p
        if k > 1:
            prod = _poly_rem(prod, self._modulus, p)
        return sum(c * p**i for i, c in enumerate(prod))

    def _find_generator(self):
        """Return (g, [g**0, ..., g**(q-2)]) for the first g generating the multiplicative group."""
        q = self.q
        for g in range(1, q):
            powers, x = [1], g
            while x != 1 and len(powers) < q:
                powers.append(x)
                x = self._poly_mul(x, g)
            if len(powers) == q - 1:
                return g, powers
        raise AssertionError("no primitive element found")  # cannot happen for a field

    def add(self, a, b):
        """Return a + b in the field."""
        return int(self.add_table[a, b])

    def sub(self, a, b):
        """Return a - b in the field."""
        return int(self.add_table[a, self._neg[b]])

    def neg(self, a):
        """Return -a in the field."""
        return int(self._neg[a])

    def mul(self, a, b):
        """Return a * b in the field."""
        return int(self.mul_table[a, b])

    def inv(self, a):
        """Return the multiplicative inverse of a; raise ValueError if a == 0."""
        if a == 0:
            raise ValueError("0 has no inverse")
        return int(self._exp[(-self._log[a]) % (self.q - 1)])

    def pow(self, a, e):
        """Return a**e in the field (e may be negative if a != 0)."""
        if a == 0:
            if e < 0:
                raise ValueError("0 has no inverse")
            return 1 if e == 0 else 0
        return int(self._exp[(self._log[a] * e) % (self.q - 1)])

    def primitive_element(self):
        """Return a generator of the multiplicative group of the field."""
        return self._primitive


# ------------------------------------------------------------ graph constructions

def projective_points(q):
    """Return the points of PG(2, q): nonzero vectors of GF(q)^3 with first nonzero entry 1, sorted."""
    return [v for v in itertools.product(range(q), repeat=3)
            if any(v) and next(c for c in v if c) == 1]


def projective_plane_incidence(q):
    """Return (n, edges) of the point-line incidence graph of PG(2, q); points are 0..m-1, lines m..2m-1."""
    F = GF(q)
    pts = np.array(projective_points(q), dtype=np.int64)
    m = len(pts)
    mul, add = F.mul_table, F.add_table
    # dot[i, j] = point_i . line_j over GF(q); lines use the same vectors as points.
    terms = [mul[pts[:, None, c], pts[None, :, c]] for c in range(3)]
    dot = add[add[terms[0], terms[1]], terms[2]]
    rows, cols = np.nonzero(dot == 0)
    return 2 * m, [(int(i), m + int(j)) for i, j in zip(rows, cols)]


def voltage_lift(base_n, darts, m):
    """Lift a base graph with Z_m voltages: dart (u, v, a) joins u*m+g to v*m+(g+a)%m; return (base_n*m, edges)."""
    edges = set()
    for u, v, a in darts:
        for g in range(m):
            x, y = u * m + g, v * m + (g + a) % m
            if x != y:
                edges.add((min(x, y), max(x, y)))
    return base_n * m, sorted(edges)


def haar_graph(m, S):
    """Return (2m, edges) of the Haar graph of Z_m with connection set S: a_i=i joins b_j=m+j for j-i in S."""
    shifts = sorted({s % m for s in S})
    return 2 * m, [(i, m + (i + s) % m) for i in range(m) for s in shifts]


# ------------------------------------------------------------------ graph queries

def adjacency(n, edges):
    """Return adjacency lists: a sorted list of distinct neighbours for each vertex 0..n-1."""
    nbrs = [set() for _ in range(n)]
    for u, v in edges:
        nbrs[u].add(v)
        nbrs[v].add(u)
    return [sorted(s) for s in nbrs]


def max_degree(n, edges):
    """Return the largest vertex degree (0 for an empty graph)."""
    return max((len(a) for a in adjacency(n, edges)), default=0)


def is_bipartite(n, edges):
    """Return True if the graph has no odd cycle (and no self-loop)."""
    adj = adjacency(n, edges)
    color = [-1] * n
    for start in range(n):
        if color[start] != -1:
            continue
        color[start] = 0
        stack = [start]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return False
    return True


def _balls(n, edges, D):
    """Return, per vertex, a bitmask of all vertices within distance D (bit w set = w is reachable)."""
    adj = adjacency(n, edges)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:  # nothing grew: further rounds change nothing
            break
        reach = new
    return reach


def within_diameter(n, edges, D):
    """Return True if every pair of vertices is within distance D (False if disconnected)."""
    full = (1 << n) - 1
    return all(r == full for r in _balls(n, edges, D))


def bad_pairs(n, edges, D):
    """Return the number of unordered vertex pairs at distance more than D (unreachable pairs count)."""
    return sum(n - r.bit_count() for r in _balls(n, edges, D)) // 2


def relabel(edges):
    """Return (n, edges) with vertex labels compacted to 0..n-1 in sorted order of the old labels."""
    new = {old: i for i, old in enumerate(sorted({x for e in edges for x in e}))}
    return len(new), [(new[u], new[v]) for u, v in edges]
