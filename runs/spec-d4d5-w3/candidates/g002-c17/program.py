import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known bases: projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite regular-graph annealing (diameter D, both sides of size h).
#
# State: d-regular bipartite graph on A = {0..h-1} and B = {h..2h-1}, stored as
# an edge list E of absolute (a, b) pairs, a set S of the same pairs, and
# adjacency lists. Moves are double-edge switches, which keep every degree
# fixed. Cost = number of ordered vertex pairs at distance > D, computed with
# big-integer bitsets. Zero cost means the graph is valid for diameter D.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
    """Ordered pairs (v, w) with dist(v, w) > D, using bitset ball expansion."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - x.bit_count() for x in ball)


def _set_pairs(E, S, adj, i, j, na1, nb1, na2, nb2):
    """Replace edges E[i], E[j] by (na1, nb1), (na2, nb2), keeping S and adj in sync."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    S.discard((a1, b1))
    S.discard((a2, b2))
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    E[i] = (na1, nb1)
    E[j] = (na2, nb2)
    S.add((na1, nb1))
    S.add((na2, nb2))
    adj[na1].append(nb1)
    adj[nb1].append(na1)
    adj[na2].append(nb2)
    adj[nb2].append(na2)


def _random_regular(h, d, rng):
    """Random simple d-regular bipartite graph with sides of size h, or None on failure."""
    S = set()
    E = []
    adj = [[] for _ in range(2 * h)]
    for _ in range(d):
        ok = False
        for _ in range(300):
            p = list(range(h))
            rng.shuffle(p)
            if all((i, h + p[i]) not in S for i in range(h)):
                ok = True
                break
        if not ok:
            return None
        for i in range(h):
            e = (i, h + p[i])
            S.add(e)
            E.append(e)
            adj[i].append(h + p[i])
            adj[h + p[i]].append(i)
    return E, S, adj


def _attempt(h, d, D, rng, t_end):
    """Time-bounded simulated annealing from a random start. Returns (n, edges) or None."""
    init = _random_regular(h, d, rng)
    if init is None:
        return None
    E, S, adj = init
    n = 2 * h
    cost = _cost(n, adj, D)
    if cost == 0:
        return n, list(E)
    t0 = time.monotonic()
    span = t_end - t0
    if span <= 0:
        return None
    T0, T1 = 3.0, 0.2
    while True:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _set_pairs(E, S, adj, i, j, a1, b2, a2, b1)
        c2 = _cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return n, list(E)
        else:
            _set_pairs(E, S, adj, i, j, a1, b1, a2, b2)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence graph: diameter 3, d-regular when d-1 is a prime power.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Main search: annealed d-regular bipartite graphs of growing side size h.
    moore_h = lib.moore_bound(d, D) // 2
    h_lo = best_n // 2
    step = max(1, (moore_h - h_lo) // 8)
    while time.monotonic() < deadline and h_lo < moore_h:
        h_try = min(moore_h, h_lo + step)
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.25 * (deadline - now)))
        res = _attempt(h_try, d, D, rng, slice_end)
        ok = False
        if res is not None:
            n_c, e_c = res
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                best_n = n_c
                ok = True
        if ok:
            h_lo = h_try
            step *= 2
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
