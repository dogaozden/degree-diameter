import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective plane, Araujo-Pardo-Lopez, generalized quadrangle.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Bipartite Moore bound 2 * sum_{i<D} (d-1)^i for d >= 2."""
    if d <= 1:
        return 2 if D >= 1 else 1
    return 2 * sum((d - 1) ** i for i in range(D))


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
        return lib.araujo_lopez_graph(q)
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


# ----------------------------------------------------------------------------
# Main new family: random d-regular bipartite graphs (as edge lists between
# sides A = 0..N-1 and B = 0..N-1), improved by edge switches that minimise
# the number of vertex pairs at distance > D. Not cyclic / not lifts.
# ----------------------------------------------------------------------------

def _ball_cost(N, E, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        bb = N + b
        adj[a].append(bb)
        adj[bb].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _circulant_start(N, d, rng):
    """Simple d-regular bipartite circulant, then many random valid switches."""
    E = [[a, (a + k) % N] for a in range(N) for k in range(d)]
    S = {(a, b) for a, b in E}
    m = len(E)
    for _ in range(10 * m):
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        E[i] = [a1, b2]
        E[j] = [a2, b1]
    return E, S


def _anneal(N, d, D, rng, deadline):
    """Anneal edge switches towards zero bad pairs. Returns (success, best_edge_list)."""
    E, S = _circulant_start(N, d, rng)
    m = len(E)
    cost = _ball_cost(N, E, D)
    best_cost = cost
    best_E = [list(e) for e in E]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 1.2 * (0.08 / 1.2) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        c2 = _ball_cost(N, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_E = [list(e) for e in E]
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    return best_cost == 0, best_E


def _search_regular(d, D, N0, deadline, rng, on_found):
    """Grow the side size N; each success is reported via on_found(N, E)."""
    best_N = 0
    N = N0
    step = max(2, N0 // 10)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        budget = min(remaining, max(2.0, 0.4 * remaining))
        ok, E = _anneal(N, d, D, rng, time.monotonic() + budget)
        if ok:
            on_found(N, E)
            best_N = N
            N = N + step
        elif best_N:
            step = max(1, step // 2)
            N = best_N + step
        else:
            N = max(d + 1, int(N * 0.9))


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = _moore(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n:
            try:
                ok = lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best = (n, e)
                best_n = n

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        try:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])
        except Exception:
            pass

    if D >= 4:
        try:
            qg = next((q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)), None)
            if qg is not None:
                gq = _gq_w(qg)
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing to search.
    if best_n >= moore or D < 3:
        return best

    def on_found(N, E):
        edges = [(a, N + b) for a, b in E]
        consider(2 * N, edges)

    S = sum((d - 1) ** i for i in range(D))
    N0 = max(d + 1, int(0.3 * S))
    try:
        _search_regular(d, D, N0, deadline, rng, on_found)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
