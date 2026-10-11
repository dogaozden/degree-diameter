"""Bi-Cayley-style voltage lifts of the PG(2,q) incidence graph, searched by annealing.

Base graph: incidence graph of PG(2,q), q the largest prime power with q+1 <= d.
Lift: Z_m voltages on each base edge (lib.voltage_lift), so the result has n0*m
vertices and keeps degree q+1 and bipartiteness. The annealer minimises the number of
ordered pairs at distance > D using bitmask balls. Each feasible m is kept and the
search moves to the next m. Every candidate is re-checked with lib.is_valid, and the
fallback is K_{d,d} or PG(2,q), so the output is always valid.
"""
import math
import random
import time

import lib


def _pg_base(d):
    """Return (n0, edges0) of PG(2,q) incidence for the largest prime power q with q+1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n0, e0 = lib.projective_plane_incidence(q)
            return n0, e0
    return None


def _lift_cost(N, adj, D):
    """Number of ordered (vertex, vertex) pairs at distance > D (0 means diameter <= D)."""
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


def _build_adj(N, m, edges0, volt):
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(edges0, volt):
        for g in range(m):
            x = u * m + g
            y = v * m + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _anneal_lift(n0, edges0, m, D, deadline, rng, max_iters):
    """Anneal Z_m voltages on the base edges. Returns the voltage list on success, else None."""
    E = len(edges0)
    N = n0 * m
    volt = [rng.randrange(m) for _ in range(E)]
    cur = _lift_cost(N, _build_adj(N, m, edges0, volt), D)
    T = 1.5
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(E)
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        c = _lift_cost(N, _build_adj(N, m, edges0, volt), D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volt[i] = old
        T = max(0.3, T * 0.998)
    return volt if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    base = _pg_base(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)  # PG(2,q) has diameter 3, so valid for D >= 3
        if D >= 4:
            fails = 0
            m = 2
            while time.monotonic() < deadline and fails < 3 and m < 60:
                if n0 * m > best_n:
                    remaining = deadline - time.monotonic()
                    slice_end = time.monotonic() + max(2.0, 0.25 * remaining)
                    slice_end = min(slice_end, deadline)
                    volt = None
                    while volt is None and time.monotonic() < slice_end:
                        volt = _anneal_lift(n0, e0, m, D, slice_end, rng, 3000)
                    if volt is not None:
                        darts = [(u, v, a) for (u, v), a in zip(e0, volt)]
                        n, e = lib.voltage_lift(n0, darts, m)
                        consider(n, e)
                        fails = 0
                    else:
                        fails += 1
                m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
