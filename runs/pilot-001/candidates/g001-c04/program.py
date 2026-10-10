import random
import time
import lib


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # D = 3: the point-line incidence graph of PG(2, q) has degree q+1 <= d
    # for any prime power q <= d-1. Use the largest such q (the exact Moore-type
    # construction when d-1 is itself a prime power).
    best = None
    exact_plane = False
    if D == 3:
        q = _largest_prime_power_at_most(d - 1)
        if q is not None:
            n, edges = lib.projective_plane_incidence(q)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                exact_plane = (q == d - 1)
    if exact_plane:
        return best

    if best is None:
        best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    # Random Haar-graph (Z_m) search for larger orders, keeping the largest valid result.
    rng = random.Random(seed)
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
            if found[0] > best[0]:
                best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best
