import random
import time
import lib

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1

    # D = 3, d-1 a prime power: projective plane incidence graph (optimal).
    if D == 3 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # D = 3, d-2 a prime power (q >= 3): Araujo-Pardo & Lopez record construction.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, edges = lib.araujo_lopez_graph(d - 2)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass

    # Fallback: random Haar graph search, always-valid K_{d,d} as the floor.
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
