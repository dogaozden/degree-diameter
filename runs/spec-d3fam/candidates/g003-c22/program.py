import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Record-level constructions (kept as the first candidates; they set the floor).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley lifts over Z_m with k base vertices per side, found by
# annealing directly on the diameter condition, with bitset reachability.
#
# Vertices: A_{i,g} = i*m + g and B_{j,h} = (k+j)*m + h.
# A dart (i, j, s) joins A_{i,g} to B_{j,(g+s) mod m} for every g.
# Each layer L is a permutation sigma_L of range(k) with one dart (i, sigma_L(i), s)
# per i, so every A and B vertex gets exactly one dart per layer: degree d, bipartite.
#
# Translation by Z_m is an automorphism, so it suffices to check the 2k
# representatives A_{i,0} and B_{j,0}.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _cost(k, m, D, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * m
    nbr = [0] * N
    for i, j, s in darts:
        ai = i * m
        bj = (k + j) * m
        for g in range(m):
            a = ai + g
            b = bj + (g + s) % m
            nbr[a] |= 1 << b
            nbr[b] |= 1 << a
    total = 0
    sources = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    for src in sources:
        vis = 1 << src
        front = vis
        for _ in range(D):
            nxt = 0
            x = front
            while x:
                lb = x & -x
                nxt |= nbr[lb.bit_length() - 1]
                x ^= lb
            nxt &= ~vis
            if not nxt:
                break
            vis |= nxt
            front = nxt
        total += N - vis.bit_count()
    return total


def _edges(k, m, darts):
    """Edge list of the bi-Cayley graph described by darts."""
    E = []
    for i, j, s in darts:
        for g in range(m):
            E.append((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, E


def _anneal(k, m, d, D, rng, deadline, budget):
    """Simulated annealing over shifts and layer permutations; returns darts with cost 0, or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    cost = _cost(k, m, D, darts)

    start = time.monotonic()
    span = max(1e-3, min(budget, deadline - start))
    end = start + span

    while cost > 0:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - start) / span
        T = 3.0 * (0.05 ** frac)
        limit = cost - T * math.log(1.0 - rng.random())

        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
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

    return darts if cost == 0 else None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    target = lib._moore_bound(d, D)
    if best_n >= target:
        return best

    # Bold search: bi-Cayley annealing aimed strictly above the current best order.
    k_opts = [2, 3, 4, 5, 6]
    attempt = 0
    while time.monotonic() < deadline and best_n < target:
        k = k_opts[attempt % len(k_opts)]
        attempt += 1
        m = best_n // (2 * k) + 1 + rng.randrange(0, 2)  # 2*k*m > best_n
        if m < 2:
            m = 2
        remaining = deadline - time.monotonic()
        budget = max(1.0, min(remaining, 0.12 * time_limit))
        darts = _anneal(k, m, d, D, rng, deadline, budget)
        if darts is not None:
            n, e = _edges(k, m, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
