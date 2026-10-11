import random
import time
import lib

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # D = 3 constructions with known record-matching orders.
    if D == 3:
        # d-1 a prime power: incidence graph of PG(2, d-1) meets the Moore bound.
        if lib.is_prime_power(d - 1):
            n, edges = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        # d-2 a prime power (>= 3): Araujo-Pardo & Lopez construction, degree q+2 = d,
        # order 2(q^2+q+5). Matches the record for d = 11, 13, 15.
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                n, edges = lib.araujo_lopez_graph(q)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    # Fallback: random Haar-graph search, starting from K_{d,d} (always valid).
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))
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
