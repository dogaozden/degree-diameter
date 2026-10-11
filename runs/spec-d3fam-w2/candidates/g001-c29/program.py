import random
import time

import lib


def _checked(cand, d, D):
    """Return cand if it is a valid graph for (d, D), else None."""
    if cand is None:
        return None
    n, edges = cand
    try:
        if lib.is_valid(n, edges, d, D):
            return cand
    except Exception:
        pass
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if D == 3:
        # Exact projective-plane incidence graph when d-1 is a prime power (meets the Moore bound).
        if lib.is_prime_power(d - 1):
            hit = _checked(lib.projective_plane_incidence(d - 1), d, D)
            if hit:
                return hit
        # Araujo-Pardo & Lopez construction, degree q+2 with q = d-2, order 2(q^2+q+5).
        # This reaches the known records for d = 11, 13, 15 (190, 274, 374).
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                hit = _checked(lib.araujo_lopez_graph(q), d, D)
            except Exception:
                hit = None
            if hit:
                return hit

    # Fallback: randomized Haar-graph search, as in the parent program.
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
