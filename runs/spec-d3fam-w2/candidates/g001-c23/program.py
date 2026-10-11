import random
import time
import lib

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # Exact projective-plane incidence graph when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            n, edges = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass

    # Araujo-Pardo & Lopez record family for D = 3 when q = d-2 is a prime power >= 3.
    # Order 2(q^2+q+5), degree q+2 = d. Matches the records for d = 11, 13, 15.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, edges = lib.araujo_lopez_graph(d - 2)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass

    # Fallback: randomized Haar-graph search (valid by checking diameter each time).
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
