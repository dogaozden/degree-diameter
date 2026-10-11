import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d} (D >= 2), projective-plane incidence graph and the
# Araujo-Pardo-Lopez graph (D >= 3).
# ----------------------------------------------------------------------------

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
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family for D >= 3: bipartite d-regular graphs on 2h vertices (h per side),
# obtained from a Haar graph start and improved by double-edge switches that
# keep the graph simple and regular. The objective is the number of ordered
# pairs at distance > D, computed with big-integer bitset balls.
# ----------------------------------------------------------------------------

def _haar_start(h, d, rng):
    """Adjacency lists of Haar(h, S) with |S| = d (needs h >= d); A = 0..h-1, B = h..2h-1."""
    S = [0] + rng.sample(range(1, h), d - 1)
    adj = [[] for _ in range(2 * h)]
    for i in range(h):
        for s in S:
            b = h + (i + s) % h
            adj[i].append(b)
            adj[b].append(i)
    return adj


def _bad(N, adj, D):
    """Number of ordered vertex pairs at distance > D (zero means diameter <= D)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _switch(adj, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Preconditions checked by caller."""
    adj[a1][adj[a1].index(b1)] = b2
    adj[a2][adj[a2].index(b2)] = b1
    adj[b1][adj[b1].index(a1)] = a2
    adj[b2][adj[b2].index(a2)] = a1


def _anneal(h, d, D, rng, deadline):
    """Simulated annealing over double-edge switches. Returns adjacency lists or None."""
    N = 2 * h
    adj = _haar_start(h, d, rng)
    cost = _bad(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        f = (now - t0) / span
        T = 0.01 * cost * (1.0 - f) + 0.2

        a1 = rng.randrange(h)
        b1 = rng.choice(adj[a1])
        a2 = rng.randrange(h)
        b2 = rng.choice(adj[a2])
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adj[a1] or b1 in adj[a2]:
            continue

        _switch(adj, a1, b1, a2, b2)
        c2 = _bad(N, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _switch(adj, a1, b2, a2, b1)  # revert
    return adj if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

        # Annealed d-regular bipartite search above the current best order.
        step = 4
        while time.monotonic() < deadline - 0.5:
            best_h = best_n // 2
            target = best_h + step
            remaining = deadline - time.monotonic()
            chunk = max(2.0, remaining * 0.35)
            sub_deadline = min(deadline, time.monotonic() + chunk)
            adj = _anneal(target, d, D, rng, sub_deadline)
            if adj is not None:
                E = [(a, b) for a in range(target) for b in adj[a]]
                consider(2 * target, E)
                if best_n // 2 >= target:
                    step = min(step * 2, 32)
                else:
                    step = max(1, step // 2)
            else:
                step = max(1, step // 2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
