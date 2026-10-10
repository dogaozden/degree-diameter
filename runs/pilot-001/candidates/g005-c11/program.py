import itertools
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D.

    Cost = number of vertex pairs at distance > D. Returns S with cost 0, or None.
    """
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:  # accept sideways moves to escape plateaus
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices.

    Returns (n, edges) with zero bad pairs, or None if the budget runs out.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        if m > 1:
            darts[j][2] = (old + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:  # accept plateau moves too
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _extend_lift(d, D, k, m, rng, iters, deadline):
    """Orbit extension: close a (d-1)-regular Z_m lift, then attach one new A-orbit and one new B-orbit.

    Stage 1 hill-climbs voltages of a (d-1)-regular base with k+k vertices until the lift
    has diameter <= D. Stage 2 adds base vertices newA (id 2k) and newB (id 2k+1). Each
    existing base vertex has one spare degree slot, so newA takes d-1 spare B-slots,
    newB takes d-1 spare A-slots, and newA-newB is one more dart; every base vertex ends
    with degree d. Stage 2 hill-climbs only the new voltages. Returns (n, edges) or None.
    """
    if k < d - 1 or m < 2:
        return None

    def evaluate(darts, base_n):
        n, e = lib.voltage_lift(base_n, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    # Stage 1: (d-1)-regular base on k+k vertices.
    perms = [rng.sample(range(k), k) for _ in range(d - 1)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]
    n, e, c = evaluate(darts, 2 * k)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate(darts, 2 * k)
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c != 0:
        return None

    # Stage 2: attach the new orbit pair using the spare slots.
    newA, newB = 2 * k, 2 * k + 1
    spareB = rng.sample(range(k, 2 * k), d - 1)
    spareA = rng.sample(range(k), d - 1)
    ext = ([[newA, b, rng.randrange(m)] for b in spareB]
           + [[a, newB, rng.randrange(m)] for a in spareA]
           + [[newA, newB, rng.randrange(m)]])
    base_n = 2 * k + 2
    n, e, c = evaluate(darts + ext, base_n)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(ext))
        old = ext[j][2]
        ext[j][2] = (old + rng.randrange(0, m)) % m
        n2, e2, c2 = evaluate(darts + ext, base_n)
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            ext[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane with largest prime power q <= d - 1.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # D >= 4: generalized quadrangle W(q) with q + 1 <= d (diameter 4 <= D).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Mixed search: Haar graphs, random-base voltage lifts, and orbit extensions.
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        r = rng.random()
        if r < 0.4 and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        elif r < 0.7 and d >= 2:
            k = d - 1 + rng.randrange(0, 3)
            m = max(2, best_n // (2 * k + 2) + 1)
            res = _extend_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
        else:
            k = rng.choice([1, 2, 3, 4])
            m = max(2, best_n // (2 * k) + 1)
            res = _search_lift(d, D, k, m, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
