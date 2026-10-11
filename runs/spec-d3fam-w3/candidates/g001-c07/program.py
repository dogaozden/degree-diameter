import random
import time

import lib


def _largest_prime_power_leq(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _valid_or_none(graph, d, D):
    n, edges = graph
    if lib.is_valid(n, edges, d, D):
        return graph
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # Algebraic constructions for diameter 3 (the target cases).
    if D == 3:
        makers = []
        # Optimal: incidence graph of PG(2, d-1), degree d.
        if lib.is_prime_power(d - 1):
            makers.append(lambda: lib.projective_plane_incidence(d - 1))
        # Araujo-Pardo & Lopez record: degree q+2 with q = d-2, order 2(q^2+q+5).
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            makers.append(lambda: lib.araujo_lopez_graph(d - 2))
        # Safe fallback: PG(2, q) for the largest prime power q <= d-1, degree q+1 <= d.
        q = _largest_prime_power_leq(d - 1)
        if q is not None:
            makers.append(lambda: lib.projective_plane_incidence(q))

        best_alg = None
        for make in makers:
            try:
                g = _valid_or_none(make(), d, D)
            except Exception:
                g = None
            if g is not None and (best_alg is None or g[0] > best_alg[0]):
                best_alg = g
        if best_alg is not None:
            return best_alg

    # General fallback: random Haar-graph search (also used for other D).
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
