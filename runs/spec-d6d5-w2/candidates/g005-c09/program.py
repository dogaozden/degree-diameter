import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction used here: voltage lifts of the projective-plane incidence graph
# PG(2, q) over small groups (cyclic or semidirect Z_m x| Z_k).
#
# A lift of a bipartite base graph by a group of order G has base_n * G
# vertices and keeps the base degree, and it stays bipartite because every
# dart goes from the point side to the line side. Voltages are annealed so the
# lift has diameter <= D. Every candidate goes through lib.is_valid before it
# can replace the current best, and K_{d,d} (or the PG incidence graph) is the
# fallback.
# ----------------------------------------------------------------------------


def _best_pg_q(d):
    """Largest prime power q with q + 1 <= d (degree of PG(2, q) incidence)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _random_group(G, rng):
    """Return (order, mul) for a random group Z_m x| Z_k of order G, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k = rng.choice(divs)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, _ = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    return order, mul


def _translation_table(order, mul):
    """T[g][x] = mul(x, g)."""
    return [[mul(x, g) for x in range(order)] for g in range(order)]


def _lift_edges(darts, order, T):
    """Edges of the lift: dart (u, v, g) joins u*order+x to v*order+T[g][x]."""
    E = set()
    for u, v, g in darts:
        row = T[g]
        base_u = u * order
        base_v = v * order
        for x in range(order):
            E.add((base_u + x, base_v + row[x]))
    return list(E)


def _bad_ordered_pairs(N, adj, D):
    """Number of ordered pairs at distance > D (bitset ball growth)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(N - b.bit_count() for b in ball)


def _cost(darts, N, order, T, D):
    E = _lift_edges(darts, order, T)
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return _bad_ordered_pairs(N, adj, D)


def _anneal_lift(base_e, nb, order, T, D, rng, deadline):
    """Anneal voltages on base darts until the lift has diameter <= D. Returns darts or None."""
    N = nb * order
    darts = [[u, v, rng.randrange(order)] for u, v in base_e]
    cur = _cost(darts, N, order, T, D)
    temp = 3.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(len(darts))
        old = darts[i][2]
        new = rng.randrange(order)
        if new == old:
            continue
        darts[i][2] = new
        c = _cost(darts, N, order, T, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            darts[i][2] = old
        temp = max(0.5, temp * 0.999)
    return darts if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D == 2:
        return best

    q = _best_pg_q(d)
    pg_n = pg_e = None
    if q is not None:
        pg_n, pg_e = lib.projective_plane_incidence(q)
        consider(pg_n, pg_e)

    # Araujo-Pardo-Lopez record graph for d = q + 2 (diameter 3).
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar_n, ar_e = lib.araujo_lopez_graph(d - 2)
            consider(ar_n, ar_e)
        except Exception:
            pass

    # Voltage-lift search over PG(2, q) (main new family).
    moore = lib.moore_bound(d, D)
    if pg_n is not None and best_n < moore:
        nb = pg_n
        base_e = pg_e
        while time.monotonic() < deadline:
            G_lo = best_n // nb + 1
            if nb * G_lo > moore:
                break
            G = G_lo + rng.choice([0, 0, 1, 2])
            if nb * G > moore:
                G = G_lo
            g = _random_group(G, rng)
            if g is None:
                continue
            order, mul = g
            if nb * order <= best_n or nb * order > moore:
                continue
            T = _translation_table(order, mul)
            now = time.monotonic()
            slice_end = min(deadline, now + max(6.0, 0.35 * (deadline - now)))
            darts = _anneal_lift(base_e, nb, order, T, D, rng, slice_end)
            if darts is not None:
                E = _lift_edges(darts, order, T)
                consider(nb * order, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
