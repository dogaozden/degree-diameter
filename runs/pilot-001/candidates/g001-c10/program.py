import random
import time
import lib


def _largest_prime_power_at_most(q):
    for x in range(q, 1, -1):
        if lib.is_prime_power(x):
            return x
    return None


def _projective_candidate(d):
    # Incidence graph of PG(2, q) has diameter 3 and degree q + 1 <= d.
    # Use the largest prime power q <= d - 1, even when d - 1 itself is not one.
    q = _largest_pp_below = _largest_prime_power_at_most(d - 1)
    if q is None:
        return None
    n, edges = lib.projective_plane_incidence(q)
    if lib.is_valid(n, edges, d, 3):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    best = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}: always valid

    if D == 3:
        cand = _projective_candidate(d)
        if cand is not None and cand[0] > best[0]:
            best = cand
        if lib.is_prime_power(d - 1):
            # Already optimal at this degree; no search needed.
            return best

    rng = random.Random(seed)
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if n > best[0] and lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
