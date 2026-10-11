import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic bases.
#   PG(2, q) incidence: diameter 3, degree q + 1.
#   W(q) generalized-quadrangle incidence: diameter 4, degree q + 1.
# Both are stored with points on side 0 (indices < half) and lines on side 1.
# ----------------------------------------------------------------------------

def _largest_pp(limit):
    """Largest prime power q with 2 <= q <= limit, or None."""
    for q in range(limit, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of the points and totally isotropic lines of W(q) (diameter 4)."""
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
    edges = []
    nlines = 0
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
            for p in L:
                edges.append((p, P + nlines))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nlines += 1
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Regular voltage lifts of an algebraic base over Z_m.
#
# Each base edge (u, w) carries a voltage a in Z_m. The lift has vertices
# (x, g) = x*m + g and edges (u, g) -- (w, g + a). Degrees and bipartiteness
# are inherited. The lift is Z_m-symmetric, so distances from (x, 0) for each
# base vertex x decide the diameter.
# ----------------------------------------------------------------------------

def _lift_cost(B, m, Eu, Ew, volt, D):
    """Number of (base representative, vertex) pairs at distance > D. Zero iff diameter <= D."""
    N = B * m
    nb = [[] for _ in range(N)]
    for e in range(len(Eu)):
        u = Eu[e] * m
        w = Ew[e] * m
        a = volt[e]
        for g in range(m):
            x = u + g
            y = w + (g + a) % m
            nb[x].append(y)
            nb[y].append(x)
    ball = [1 << i for i in range(N)]
    for _ in range(D):
        new = [0] * N
        for i in range(N):
            x = ball[i]
            for j in nb[i]:
                x |= ball[j]
            new[i] = x
        ball = new
    return sum(N - ball[x * m].bit_count() for x in range(B))


def _lift_edges(B, m, Eu, Ew, volt):
    """Edge list of the lift (simple, since the base is simple)."""
    edges = set()
    for e in range(len(Eu)):
        u = Eu[e] * m
        w = Ew[e] * m
        a = volt[e]
        for g in range(m):
            x = u + g
            y = w + (g + a) % m
            edges.add((min(x, y), max(x, y)))
    return B * m, sorted(edges)


def _lift_search(B, Eu, Ew, d, D, m, slice_end, rng):
    """Anneal voltages in Z_m until the lift has diameter <= D. Returns (n, edges) or None."""
    E = len(Eu)
    volt = [rng.randrange(m) for _ in range(E)]
    cost = _lift_cost(B, m, Eu, Ew, volt, D)
    T = 2.0
    while cost > 0 and time.monotonic() < slice_end:
        e = rng.randrange(E)
        old = volt[e]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[e] = new
        c2 = _lift_cost(B, m, Eu, Ew, volt, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            volt[e] = old
        T = max(0.2, T * 0.998)
    if cost != 0:
        return None
    n, edges = _lift_edges(B, m, Eu, Ew, volt)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    base = None  # algebraic base used for voltage lifts when D >= 5

    if D >= 3:
        q = _largest_pp(d - 1)
        if q is not None:
            pg = lib.projective_plane_incidence(q)
            consider(pg[0], pg[1])
            base = pg
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass

    if D >= 4:
        q = _largest_pp(min(d - 1, 7))
        if q is not None:
            gq = _gq_w(q)
            consider(gq[0], gq[1])
            base = gq  # prefer the diameter-4 base for lifts

    # Bold change for D >= 5: take a generalized-quadrangle base (or PG fallback)
    # and search Z_m voltage lifts of growing order. Lifts keep degree and
    # bipartiteness, so only the diameter must be repaired.
    if D >= 5 and base is not None:
        n0, e0 = base
        half = n0 // 2
        Eu, Ew = [], []
        for u, w in e0:
            a, b = (u, w) if u < w else (w, u)
            Eu.append(a)
            Ew.append(b - half if False else b)
        # Lift base indices: side-0 vertices are 0..half-1, side-1 are half..n0-1.
        # Use compact indices so the lift has n0 * m vertices.
        Ew = [b for b in Ew]
        m = 2
        while time.monotonic() < deadline and n0 * m <= 4000:
            now = time.monotonic()
            remaining = deadline - now
            slice_end = now + max(2.0, 0.45 * remaining)
            slice_end = min(slice_end, deadline)
            res = _lift_search(n0, Eu, Ew, d, D, m, slice_end, rng)
            if res is not None:
                consider(res[0], res[1])
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
