"""Helper library for graph-construction programs (import as `import lib`).

Graphs are given as `(n, edges)`: `n` vertices labelled 0..n-1 and `edges`, a list of
`(u, v)` pairs. Edges are undirected. Uses only the standard library and numpy.
"""
import itertools
import math

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


def cyclic_group(m):
    """Return (order, mul, inv) for Z_m, with elements 0..m-1."""
    return m, (lambda x, y: (x + y) % m), (lambda x: (-x) % m)


def semidirect_group(m, k, r):
    """Return (order, mul, inv) for Z_m x|_r Z_k, element (a, b) coded as a*k+b; needs r^k = 1 mod m and gcd(r, m) = 1."""
    if m < 1 or k < 1 or math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
        raise ValueError(f"need gcd(r, m) = 1 and r^k = 1 mod m, got m={m} k={k} r={r}")
    r %= m
    powers = [pow(r, b, m) for b in range(k)]   # powers[b] = r^b mod m

    def mul(x, y):
        """(a, b) * (c, d) = (a + r^b * c, b + d)."""
        a, b = divmod(x, k)
        c, d = divmod(y, k)
        return ((a + powers[b] * c) % m) * k + (b + d) % k

    def inv(x):
        """Inverse of (a, b) is (-r^(-b) * a, -b)."""
        a, b = divmod(x, k)
        nb = (-b) % k
        return ((-powers[nb] * a) % m) * k + nb

    return m * k, mul, inv


def group_lift(base_n, darts, order, mul):
    """Lift a base graph over a finite group: dart (u, v, g) joins u*order+x to v*order+mul(x, g) for all x; return (base_n*order, edges).

    A loop dart (u, u, g) gives the same edges as (u, u, inverse of g), so list a loop only once.
    """
    edges = set()
    for u, v, g in darts:
        for x in range(order):
            a, b = u * order + x, v * order + mul(x, g)
            if a != b:
                edges.add((min(a, b), max(a, b)))
    return base_n * order, sorted(edges)


# ------------------------------------------------------------------ graph queries

def adjacency(n, edges):
    """Return adjacency lists: a sorted list of distinct neighbours for each vertex 0..n-1."""
    nbrs = [set() for _ in range(n)]
    for u, v in edges:
        nbrs[u].add(v)
        nbrs[v].add(u)
    return [sorted(s) for s in nbrs]


def max_degree(n, edges):
    """Return the largest vertex degree (0 for an empty graph). Duplicate edges are ignored."""
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


def _moore_bound(d, D):
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def is_valid(n, edges, d, D):
    """True iff (n, edges) is exactly what the scorer accepts: labels in range, no self-loops, no duplicate edges, max degree <= d, bipartite, diameter <= D."""
    if not _is_int(n) or not 1 <= n <= 2_000_000:
        return False
    seen = set()
    degree = {}
    for e in edges:
        if not isinstance(e, (list, tuple)) or len(e) != 2:
            return False
        u, v = e
        if not _is_int(u) or not _is_int(v) or not (0 <= u < n and 0 <= v < n) or u == v:
            return False
        key = (u, v) if u < v else (v, u)
        if key in seen:
            return False
        seen.add(key)
        degree[u] = degree.get(u, 0) + 1
        degree[v] = degree.get(v, 0) + 1
    if any(k > d for k in degree.values()):
        return False
    # Cheap rejections first, so a huge n never reaches the O(n^2)-bit step.
    if n > _moore_bound(d, D) or (n > 1 and len(seen) < n - 1):
        return False
    return is_bipartite(n, list(seen)) and within_diameter(n, list(seen), D)


def araujo_lopez_graph(q):
    """(q+2)-regular bipartite graph of order 2(q^2+q+5) and diameter 3 (Araujo-Pardo & López, arXiv 2005.02427): PG(2,q) incidence plus 8 vertices. Record order for d = q+2 when d-1 is not a prime power."""
    if q < 3 or not is_prime_power(q):
        raise ValueError(f"q must be a prime power >= 3, got {q}")
    F = GF(q)
    a = 2  # any field element other than 0 and 1
    ids = {}
    edges = set()

    def vid(name):
        return ids.setdefault(name, len(ids))

    def add(point, line):
        edges.add((vid(point), vid(line)))

    # Construction, with PG(2,q) points (x,y), P_m, P and lines [m,b], L_c, L:
    #  1. Start from the PG(2,q) incidence graph, which is (q+1)-regular.
    #  2. Delete the edge ((0,a), [0,a]).
    #  3. Add 8 vertices: points Q0, (0,0)^, (0,1)^, (0,a)^ and lines M0, [0,0]^, [0,1]^, [0,a]^.
    #  4. Add edges: P-M0, L-Q0; Q0 to [0,j]^ and to [0,i]; M0 to (0,j)^ and to (0,i);
    #     P_0-[0,a]^, L_0-(0,a)^, (0,0)^-[0,1]^, (0,1)^-[0,0]^; (0,j)^-[t,j] and [0,j]^-(t,j),
    #     for j in {0,1,a}, i not in {0,1}, all t.
    #  5. Match the vertices still of degree q+1: P_i-L_i, and (x,y)-[x,y]. Every degree is now q+2.
    for m in range(q):
        for b in range(q):
            for x in range(q):
                add(("pt", x, F.add(F.mul(m, x), b)), ("ln", m, b))  # (x, mx+b) on [m,b]
    for m in range(q):
        add(("P", m), ("L",))                      # P_m on L
        for b in range(q):
            add(("P", m), ("ln", m, b))            # P_m on [m,b]
    for c in range(q):
        add(("P",), ("L", c))                      # P on L_c
        for y in range(q):
            add(("pt", c, y), ("L", c))            # (c,y) on L_c
    add(("P",), ("L",))                            # P on L
    edges.discard((vid(("pt", 0, a)), vid(("ln", 0, a))))

    J = (0, 1, a)
    I = [i for i in range(q) if i not in (0, 1)]
    add(("P",), ("M0",))
    add(("Q0",), ("L",))
    for j in J:
        add(("Q0",), ("hl", j))
        add(("hp", j), ("M0",))
    for i in I:
        add(("Q0",), ("ln", 0, i))
        add(("pt", 0, i), ("M0",))
    add(("P", 0), ("hl", a))
    add(("hp", a), ("L", 0))
    add(("hp", 0), ("hl", 1))
    add(("hp", 1), ("hl", 0))
    for j in J:
        for t in range(q):
            add(("hp", j), ("ln", t, j))
            add(("hl", j), ("pt", t, j))

    degree = {}
    for u, v in edges:
        degree[u] = degree.get(u, 0) + 1
        degree[v] = degree.get(v, 0) + 1
    matching = [(("P", i), ("L", i)) for i in range(q)]
    matching += [(("pt", x, y), ("ln", x, y)) for x in range(q) for y in range(q)]
    for point, line in matching:
        u, v = vid(point), vid(line)
        if degree.get(u) == q + 1 and degree.get(v) == q + 1:
            edges.add((u, v))
    return len(ids), sorted(edges)


# ---------------------------------------------------------------- running C code

def graph_to_text(n, edges):
    """The "n m" + one "u v" line per edge text format used by C search engines."""
    return f"{n} {len(edges)}\n" + "".join(f"{u} {v}\n" for u, v in edges)


def parse_graph_text(text):
    """Inverse of graph_to_text: returns (n, edges). Raises ValueError on malformed text."""
    nums = text.split()
    if len(nums) < 2:
        raise ValueError("C output is empty or truncated")
    n, m = int(nums[0]), int(nums[1])
    if len(nums) < 2 + 2 * m:
        raise ValueError(f"C output promised {m} edges but has {(len(nums) - 2) // 2}")
    return n, [(int(nums[2 + 2 * i]), int(nums[3 + 2 * i])) for i in range(m)]


def run_c(source, args, stdin_graph=None, timeout=60.0):
    """Compile C source once (cached by hash, cc -O2 -std=c11 -lm), run it as `prog *args`.

    stdin gets `stdin_graph` = (n, edges) in graph_to_text format, or "0 0" if None.
    Returns stdout text. Raises RuntimeError with the compiler or program error on failure,
    so broken C shows up clearly instead of silently scoring low.
    """
    import hashlib
    import os
    import subprocess
    import tempfile

    cache = os.path.join(tempfile.gettempdir(), "evolve-c-cache")
    os.makedirs(cache, exist_ok=True)
    exe = os.path.join(cache, hashlib.sha256(source.encode()).hexdigest()[:20])
    if not os.path.exists(exe):
        src = f"{exe}.{os.getpid()}.c"
        tmp = f"{exe}.{os.getpid()}.tmp"
        with open(src, "w") as f:
            f.write(source)
        cc = os.environ.get("CC", "cc")
        r = subprocess.run([cc, "-O2", "-std=c11", "-o", tmp, src, "-lm"],
                           capture_output=True, text=True, timeout=120)
        os.remove(src)
        if r.returncode != 0:
            raise RuntimeError("C compile failed:\n" + r.stderr[-2000:])
        os.replace(tmp, exe)
    stdin = graph_to_text(*stdin_graph) if stdin_graph else "0 0\n"
    try:
        r = subprocess.run([exe, *map(str, args)], input=stdin, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"C program ran past its {timeout:.1f}s timeout") from None
    if r.returncode != 0:
        raise RuntimeError(f"C program exited with code {r.returncode}:\n" + r.stderr[-2000:])
    return r.stdout


def moore_bound(d, D):
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    return _moore_bound(d, D)
