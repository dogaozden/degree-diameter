import random
import time
import lib


def _largest_prime_power_leq(x):
    """Return the largest prime power q with 2 <= q <= x, or None if there is none."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
    if D == 3:
        # PG(2, q') has degree q'+1 <= d for any prime power q' <= d-1, and diameter 3.
        qp = _largest_prime_power_leq(d - 1)
        if qp is not None:
            n, edges = lib.projective_plane_incidence(qp)
            if n > best[0]:
                best = (n, edges)
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
