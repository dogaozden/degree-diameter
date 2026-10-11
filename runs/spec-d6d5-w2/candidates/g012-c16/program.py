import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic fallbacks (valid for their own diameter, used as safe starting points).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
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
# New construction: bipartite switch-annealing with incremental vertex splicing.
#
# Graphs are kept as (n, E) where every edge is a tuple (a, b) with a on the
# "left" and b on the "right". Vertices are 0..n-1.
#
#  * Seed: a Haar graph on m + m vertices (d-regular, bipartite) at an
#    optimistic size, then 2-switch annealing on the number of ordered
#    vertex pairs at distance > D. Switches keep every degree and the sides.
#  * Growth: splice in one new left and one new right vertex of degree d
#    (degrees of old vertices are unchanged), then anneal the result back
#    to diameter <= D. Repeat while successful.
# ----------------------------------------------------------------------------

def _bad(n, E, D):
    """Ordered count of (vertex, vertex) pairs at distance more than D."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(n, E, D, deadline, rng, T0=3.0):
    """Anneal 2-switches until diameter <= D. Returns the edge list or None."""
    E = list(E)
    m = len(E)
    if m < 2:
        return None
    eset = set(E)
    cur = _bad(n, E, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.1, T0 * (1.0 - (now - start) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        new = _bad(n, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return E if cur == 0 else None


def _splice(n, E, d, rng):
    """Add a left vertex n and a right vertex n+1 of degree d by splicing d edges.

    Each chosen edge (a, b) becomes (n, b) and (a, n+1); old degrees are kept.
    """
    m = len(E)
    if m < d:
        return None
    x, y = n, n + 1
    used, xs, ys, chosen = set(), set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 20000:
        tries += 1
        i = rng.randrange(m)
        if i in used:
            continue
        a, b = E[i]
        if b in xs or a in ys:
            continue
        used.add(i)
        xs.add(b)
        ys.add(a)
        chosen.append(i)
    if len(chosen) < d:
        return None
    newE = [E[i] for i in range(m) if i not in used]
    for i in chosen:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return n + 2, newE


def _haar_seed(d, D, moore, end, rng):
    """Find a valid Haar-type d-regular bipartite graph at a large size, or None."""
    m = max(d + 1, min(moore // 8, 400))
    while time.monotonic() < end and m >= d + 1:
        now = time.monotonic()
        try_end = min(end, now + max(2.0, (end - now) * 0.5))
        n, E = lib.haar_graph(m, rng.sample(range(m), d))
        out = _anneal(n, E, D, try_end, rng)
        if out is not None:
            return n, out
        m -= max(1, m // 10)
    return None


def _search(d, D, moore, start, time_limit, rng, consider, n0, E0):
    """Haar seed at a large size, then splice-and-anneal growth."""
    deadline = start + 0.85 * time_limit
    seed_end = start + 0.35 * time_limit

    cur_n, cur_E = n0, E0
    seeded = _haar_seed(d, D, moore, seed_end, rng)
    if seeded is not None:
        cur_n, cur_E = seeded
        consider(cur_n, cur_E)

    fails = 0
    while time.monotonic() < deadline - 0.5 and cur_n < moore and fails < 4:
        res = _splice(cur_n, cur_E, d, rng)
        if res is None:
            break
        n2, E2 = res
        now = time.monotonic()
        budget = min(3.0, deadline - now)
        if budget <= 0:
            break
        out = _anneal(n2, E2, D, now + budget, rng)
        if out is None:
            fails += 1
            continue
        fails = 0
        cur_n, cur_E = n2, out
        consider(cur_n, cur_E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

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

    # Bold path: annealed bipartite growth. Needs d >= 3 for a useful lift.
    if D >= 3 and d >= 3 and best_n < moore:
        n0, e0 = best
        E0 = list(e0)
        _search(d, D, moore, start, time_limit, rng, consider, n0, E0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
