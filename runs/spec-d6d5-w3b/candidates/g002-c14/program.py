"""Bi-Cayley voltage lifts over cyclic groups with many base vertices, found by
annealing and checked with bit-parallel ball growth; PG/Araujo-Lopez/K_{d,d} fallbacks."""
import math
import random
import time

import lib

BIG = 10 ** 9


def _projective_fallback(d):
    """PG(2, d-1) incidence graph (valid for D >= 3) when d-1 is a prime power."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        try:
            return lib.projective_plane_incidence(q)
        except Exception:
            return None
    return None


def _araujo_fallback(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _cost(k, m, D, darts):
    """Number of (representative, vertex) pairs at distance > D; BIG if the lift is not simple.

    The cyclic group Z_m acts transitively on each fibre, so only one representative per
    base vertex (2k of them) needs to be checked.
    """
    if len({(a[0], a[1], a[2]) for a in darts}) < len(darts):
        return BIG
    N = 2 * k * m
    nbr = [[] for _ in range(N)]
    off_b = k * m
    for i, j, s in darts:
        for g in range(m):
            a = i * m + g
            b = off_b + j * m + (g + s) % m
            nbr[a].append(b)
            nbr[b].append(a)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in nbr[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    reps = [i * m for i in range(k)] + [off_b + j * m for j in range(k)]
    return sum(N - ball[r].bit_count() for r in reps)


def _edges(k, m, darts):
    E = []
    off_b = k * m
    for i, j, s in darts:
        for g in range(m):
            E.append((i * m + g, off_b + j * m + (g + s) % m))
    return 2 * k * m, E


def _anneal(d, D, k, m, rng, deadline, max_iters):
    """Anneal voltages and per-layer matchings of a d-regular bi-Cayley base on k+k vertices."""
    darts = []  # dart index L*k + i belongs to layer L and A-vertex i
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    seen = set()
    for dt in darts:  # make the initial state simple where possible
        for _ in range(60):
            if (dt[0], dt[1], dt[2]) not in seen:
                break
            dt[2] = rng.randrange(m)
        seen.add((dt[0], dt[1], dt[2]))

    cost = _cost(k, m, D, darts)
    T = 1.0
    for _ in range(max_iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.1, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.6 or k < 2:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(m)
            c2 = _cost(k, m, D, darts)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, m, D, darts)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    have_structured = False
    if D >= 3:
        pg = _projective_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])
            have_structured = True
        ar = _araujo_fallback(d)
        if ar is not None:
            consider(ar[0], ar[1])
            have_structured = True

    # Calibration-style shortcut: small D with a known construction returns at once.
    if D == 3 and have_structured:
        return best_n, best_e

    # Main family: cyclic bi-Cayley lifts with k base vertices per side (k up to 6).
    ks = [1, 2, 2, 3, 3, 4, 6] if D >= 4 else [1, 2]
    attempt_budget = max(2.0, 0.15 * time_limit)
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(2, lo // 12)
        m = rng.randint(lo, hi)
        budget = min(deadline, time.monotonic() + attempt_budget)
        darts, c = _anneal(d, D, k, m, rng, budget, 4000)
        if c == 0:
            n, e = _edges(k, m, darts)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
