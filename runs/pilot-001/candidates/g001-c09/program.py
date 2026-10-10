import random
import time
import lib

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # D = 3: incidence graph of PG(2, q) has diameter 3 and degree q + 1.
    # Use the largest prime power q <= d - 1, which covers non-prime-power d - 1 too.
    if D == 3:
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2:
            n, edges = lib.projective_plane_incidence(q)
            if lib.is_valid(n, edges, d, D):
                return n, edges

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
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
