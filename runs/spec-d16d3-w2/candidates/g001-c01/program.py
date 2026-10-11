import random
import time
import lib


def _plane_candidate(d):
    """Incidence graph of PG(2,q) for the largest prime power q with q+1 <= d (diameter 3, degree q+1)."""
    for q in range(d - 1, 1, -1):
        if q + 1 <= d and lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    # Base candidate: projective plane incidence graph when D == 3 (n = 2(q^2+q+1), degree q+1 <= d).
    best = None
    if D == 3:
        cand = _plane_candidate(d)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    if best is None:
        best = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}: always valid

    # Haar-graph search, only useful for graphs strictly larger than the current best (n = 2m).
    m = max(d + 1, best[0] // 2 + 1)
    misses = 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if n > best[0] and lib.within_diameter(n, edges, D) and lib.is_valid(n, edges, d, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
