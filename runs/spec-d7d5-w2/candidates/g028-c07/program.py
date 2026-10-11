import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cayley-type bipartite graphs over explicit finite groups.
#
# Group G of order N with multiplication table mul[x, y]. Choose a connection
# set S of d distinct elements. Vertices A_g = g and B_g = N + g, with edges
# A_g ~ B_{g s} for s in S. Every vertex has degree d and the graph is bipartite.
# Left multiplication is an automorphism, so the diameter is at most D iff the
# balls of radius D around A_e and B_e both cover everything.
#
# This differs from the bi-Cayley lifts over semidirect products: the family
# includes non-abelian simple-group quotients PSL(2, p) and their direct
# products with cyclic groups, and the search anneals the connection set using
# an exact coverage cost computed with boolean frontier propagation.
# ----------------------------------------------------------------------------

def _finish_group(mul):
    """Given an N x N int64 multiplication table, return (N, MT, inv, e) or None.

    MT[s][g] = mul[g, s] (right multiplication by s), inv[s] is the inverse of s.
    """
    N = mul.shape[0]
    ar = np.arange(N)
    ident_rows = np.flatnonzero((mul == ar[None, :]).all(axis=1))
    if ident_rows.size == 0:
        return None
    e = int(ident_rows[0])
    rows, cols = np.nonzero(mul == e)
    if rows.size != N:
        return None
    inv = np.empty(N, dtype=np.int64)
    inv[rows] = cols
    MT = np.ascontiguousarray(mul.T)
    return N, MT, inv, e


def _psl2_table(p):
    """Multiplication table of PSL(2, p) for a prime p >= 5."""
    def code(a, b, c, d):
        return ((a * p + b) * p + c) * p + d

    lut = np.full(p ** 4, -1, dtype=np.int64)
    elems = []
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a * d - b * c) % p != 1:
            continue
        if lut[code(a, b, c, d)] != -1:
            continue
        idx = len(elems)
        elems.append((a, b, c, d))
        lut[code(a, b, c, d)] = idx
        lut[code((-a) % p, (-b) % p, (-c) % p, (-d) % p)] = idx
    N = len(elems)
    E = np.array(elems, dtype=np.int64)
    b0, b1, b2, b3 = E[:, 0], E[:, 1], E[:, 2], E[:, 3]
    mul = np.empty((N, N), dtype=np.int64)
    for x in range(N):
        a0, a1, a2, a3 = elems[x]
        c0 = (a0 * b0 + a1 * b2) % p
        c1 = (a0 * b1 + a1 * b3) % p
        c2 = (a2 * b0 + a3 * b2) % p
        c3 = (a2 * b1 + a3 * b3) % p
        mul[x] = lut[((c0 * p + c1) * p + c2) * p + c3]
    return mul


def _times_cyclic(mul, m):
    """Direct product of a group table with Z_m; element (u, a) is coded as u*m + a."""
    h = mul.shape[0]
    N = h * m
    x = np.arange(N)
    u = x // m
    a = x % m
    return mul[np.ix_(u, u)] * m + (a[:, None] + a[None, :]) % m


def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e)."""
    N = m * k
    x = np.arange(N)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    return ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k


def _sample_group(lo, hi, rng):
    """Return (N, MT, inv, e) for a random group with order in [lo, hi], or None."""
    kind = rng.random()
    if kind < 0.35:
        opts = []
        for p in (5, 7, 11, 13):
            h = p * (p * p - 1) // 2
            if h > hi:
                continue
            for m in range(1, hi // h + 1):
                if lo <= h * m <= hi:
                    opts.append((p, m))
        if not opts:
            return None
        p, m = rng.choice(opts)
        mul = _psl2_table(p)
        if m > 1:
            mul = _times_cyclic(mul, m)
        return _finish_group(mul)
    if kind < 0.9:
        for _ in range(20):
            k = rng.randint(2, 12)
            mlo = max(2, -(-lo // k))
            mhi = hi // k
            if mhi < mlo:
                continue
            m = rng.randint(mlo, mhi)
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not rs:
                continue
            res = _finish_group(_semidirect_table(m, k, rng.choice(rs)))
            if res is not None:
                return res
        return None
    N = rng.randint(lo, hi)
    x = np.arange(N)
    return _finish_group((x[:, None] + x[None, :]) % N)


def _uncovered(S, MT, inv, e, N, D):
    """Number of (start, vertex) pairs not within distance D, for starts A_e and B_e.

    Frontiers are exact-length walk sets; their union over lengths 0..D is the ball.
    """
    total = 0
    for a_start in (True, False):
        cA = np.zeros(N, dtype=bool)
        cB = np.zeros(N, dtype=bool)
        f = np.zeros(N, dtype=bool)
        f[e] = True
        if a_start:
            cA |= f
        else:
            cB |= f
        on_a = a_start
        for _ in range(D):
            g = np.zeros(N, dtype=bool)
            if on_a:
                for s in S:
                    g |= f[MT[inv[s]]]
                cB |= g
            else:
                for s in S:
                    g |= f[MT[s]]
                cA |= g
            f = g
            on_a = not on_a
        total += 2 * N - int(cA.sum()) - int(cB.sum())
    return total


def _anneal(MT, inv, e, N, d, D, rng, deadline):
    """Simulated annealing over d-element connection sets. Returns S with zero cost, or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cost = _uncovered(S, MT, inv, e, N, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.05 + 2.0 * max(0.0, 1.0 - (now - t0) / span)
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _uncovered(S, MT, inv, e, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
    return list(S) if cost == 0 else None


# ----------------------------------------------------------------------------
# Greedy pair insertion (unchanged idea): grow the order by 2 per checked step.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, rng, deadline):
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.82 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Ladder search: repeatedly look for a valid Cayley-type graph whose order
    # exceeds the current best, then move the window up.
    try:
        while time.monotonic() < search_deadline:
            lo = best_n // 2 + 1
            hi = int(lo * 1.25) + 2
            spec = None
            for _ in range(8):
                spec = _sample_group(lo, hi, rng)
                if spec is not None:
                    break
                hi = int(hi * 1.3) + 2
            if spec is None:
                continue
            N, MT, inv, e = spec
            if 2 * N <= best_n:
                continue
            slice_end = min(search_deadline, time.monotonic() + 6.0)
            S = _anneal(MT, inv, e, N, d, D, rng, slice_end)
            if S is not None:
                edges = [(g, N + int(MT[s][g])) for s in S for g in range(N)]
                consider(2 * N, edges)
    except Exception:
        pass

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
