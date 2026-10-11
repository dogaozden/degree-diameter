import random
import time

import lib


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _haar_edges(m, S):
    """Edges of the Haar graph of Z_m with connection set S: a_x ~ b_{x+s}, with b_y = m + y."""
    return [(x, m + (x + s) % m) for x in range(m) for s in S]


def _ball_cost(m, S, D, full):
    """Number of vertex pairs at distance > D, counted from a_0 and from b_0.

    The Haar graph is invariant under translation on each side, so these two sources
    determine all pairs: a-a and a-b from a_0, b-b from b_0.
    Vertex sets are bitmasks over Z_m; a shift by s is a cyclic rotation of the mask.
    """
    neg = [(m - s) % m for s in S]
    total = 0
    for side0 in (0, 1):
        seen = [0, 0]
        cur = 1
        side = side0
        seen[side] = 1
        for _ in range(D):
            shifts = S if side == 0 else neg
            nxt = 0
            for s in shifts:
                nxt |= ((cur << s) | (cur >> (m - s))) & full
            side ^= 1
            seen[side] |= nxt
            cur = nxt
        total += 2 * m - seen[0].bit_count() - seen[1].bit_count()
    return total


def _search(m, d, D, deadline, rng):
    """Hill-climb a connection set S (|S| = d, 0 in S) so the Haar graph of Z_m has diameter <= D."""
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _ball_cost(m, S, D, full)
    stale = 0
    while c:
        if time.monotonic() > deadline:
            return None
        if stale > 4000:
            S = [0] + rng.sample(range(1, m), d - 1)
            c = _ball_cost(m, S, D, full)
            stale = 0
            continue
        i = rng.randrange(1, d)
        v = rng.randrange(1, m)
        if v in S:
            stale += 1
            continue
        T = S[:]
        T[i] = v
        ct = _ball_cost(m, T, D, full)
        if ct < c:
            stale = 0
        else:
            stale += 1
        if ct <= c or rng.random() < 0.02:
            S, c = T, ct
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        for make in (_pg, _araujo):
            try:
                cand = make(d)
            except Exception:
                cand = None
            if cand is not None:
                consider(cand[0], cand[1])

    # Main search: cyclic Haar graphs (bi-Cayley over Z_m), with m increased
    # as far as the hill-climb can keep diameter <= D.
    rng = random.Random(seed * 7919 + d * 131 + D)
    target = d + 1
    while time.monotonic() < deadline:
        now = time.monotonic()
        S = _search(target, d, D, min(deadline, now + 8.0), rng)
        if S is not None:
            consider(2 * target, _haar_edges(target, S))
            target += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
