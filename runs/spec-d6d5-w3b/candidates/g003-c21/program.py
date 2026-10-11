"""Bi-Cayley search for d-regular bipartite graphs of diameter <= D.

Construction: for a group G of order N and a connection set S (|S| = d),
vertices are (g,0) and (g,1), with edges (g,0)~(s*g,1) for s in S. This
graph is bipartite, d-regular, and has 2N vertices. Right multiplication
by G is an automorphism that is transitive on each side, so diameter <= D
reduces to two BFS runs, from (e,0) and from (e,1).

Groups tried: Heisenberg groups of order p^3, affine groups AGL(1,q) of
order q(q-1), and metacyclic groups Z_m x| Z_k. Search by simulated
annealing over S, growing the order one step above the best found so far.
The fallbacks (PG(2,q) incidence, Araujo-Pardo-Lopez, W(q), K_{d,d}) are
always checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


def _isprime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


# ----------------------------------------------------------------------------
# Fallback families
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Groups
# ----------------------------------------------------------------------------

class _Group:
    """Finite group with identity 0, given by mul/inv on ints, with cached rows."""

    def __init__(self, order, mul, inv):
        self.n = order
        self.mul = mul
        self.inv = inv
        self._L = {}
        self._I = {}

    def Lrow(self, s):
        r = self._L.get(s)
        if r is None:
            m = self.mul
            r = [m(s, g) for g in range(self.n)]
            self._L[s] = r
        return r

    def Irow(self, s):
        r = self._I.get(s)
        if r is None:
            m = self.mul
            si = self.inv(s)
            r = [m(si, h) for h in range(self.n)]
            self._I[s] = r
        return r


def _heis(p):
    """Heisenberg group of order p^3; element (a,b,c) coded as (a*p+b)*p+c."""
    def dec(x):
        return x // (p * p), (x // p) % p, x % p

    def enc(a, b, c):
        return (a * p + b) * p + c

    def mul(x, y):
        a, b, c = dec(x)
        a2, b2, c2 = dec(y)
        return enc((a + a2) % p, (b + b2) % p, (c + c2 + a * b2) % p)

    def inv(x):
        a, b, c = dec(x)
        return enc((-a) % p, (-b) % p, (a * b - c) % p)

    return _Group(p ** 3, mul, inv)


def _agl(q):
    """Affine group AGL(1,q), order q(q-1); map x -> a*x + b coded as (a-1)*q + b."""
    def mul(x, y):
        a = x // q + 1
        b = x % q
        c = y // q + 1
        d = y % q
        return ((a * c) % q - 1) * q + (c * b + d) % q

    def inv(x):
        a = x // q + 1
        b = x % q
        ai = pow(a, -1, q)
        return (ai - 1) * q + (-ai * b) % q

    return _Group(q * (q - 1), mul, inv)


def _group_options(G, rng):
    """Descriptions of candidate groups of order G."""
    opts = []
    c = round(G ** (1.0 / 3))
    for p in (c - 1, c, c + 1):
        if p > 1 and p ** 3 == G and _isprime(p):
            opts.append(("heis", p))
    q = 2
    while q * (q - 1) <= G:
        if q * (q - 1) == G and _isprime(q):
            opts.append(("agl", q))
        q += 1
    for k in range(1, G):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        if len(rs) > 6:
            rs = rng.sample(rs, 6)
        for r in rs:
            opts.append(("sd", m, k, r))
    return opts


def _make(opt):
    if opt[0] == "heis":
        return _heis(opt[1])
    if opt[0] == "agl":
        return _agl(opt[1])
    _, m, k, r = opt
    order, mul, inv = lib.semidirect_group(m, k, r)
    return _Group(order, mul, inv)


# ----------------------------------------------------------------------------
# Bi-Cayley graph search
# ----------------------------------------------------------------------------

def _unreached(grp, S, D, from_one):
    """Vertices not within distance D of (e,0), or of (e,1) if from_one."""
    N = grp.n
    L = [grp.Lrow(s) for s in S]
    I = [grp.Irow(s) for s in S]
    seen = bytearray(2 * N)
    src = N if from_one else 0
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < N:
                for row in L:
                    v = N + row[u]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                h = u - N
                for row in I:
                    v = row[h]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * N - count


def _cost(grp, S, D):
    return _unreached(grp, S, D, False) + _unreached(grp, S, D, True)


def _search_group(grp, d, D, rng, deadline):
    """Anneal a connection set S of size d in grp. Returns S with cost 0, or None."""
    N = grp.n
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cost = _cost(grp, S, D)
    T = 1.0
    while cost and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(grp, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
        T = max(0.2, T * 0.9995)
    return list(S) if cost == 0 else None


def _bcg_graph(grp, S):
    N = grp.n
    edges = []
    for s in S:
        row = grp.Lrow(s)
        for g in range(N):
            edges.append((g, N + row[g]))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0)
    best_n = n0

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    half_max = moore // 2
    while time.monotonic() < hard:
        lo = best_n // 2 + 1
        if lo > half_max:
            break
        step = max(1, best_n // 60)
        G = min(half_max, lo + rng.randrange(step))
        try:
            opts = _group_options(G, rng)
            if not opts:
                continue
            grp = _make(rng.choice(opts))
            slice_end = min(hard, time.monotonic() + 6.0)
            S = _search_group(grp, d, D, rng, slice_end)
            if S is not None:
                n, e = _bcg_graph(grp, S)
                consider(n, e)
        except Exception:
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
