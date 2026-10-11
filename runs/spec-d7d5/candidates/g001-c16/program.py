import math
import random
import time
import lib


def _pairs(N, cache):
    """Factorisations N = m*k with m >= 2, k >= 1 (k = 1 is the cyclic group Z_N)."""
    key = ("pairs", N)
    if key not in cache:
        cache[key] = [(N // k, k) for k in range(1, N + 1) if N % k == 0 and N // k >= 2]
    return cache[key]


def _rs(m, k, cache):
    """Admissible multipliers r for Z_m x|_r Z_k: gcd(r, m) = 1 and r^k = 1 mod m."""
    key = ("r", m, k)
    if key not in cache:
        cache[key] = [r for r in range(1, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    return cache[key]


def _try(N, d, D, rng, cache):
    """Random bi-Cayley lift over a random group of order N with connection set of size d."""
    m, k = rng.choice(_pairs(N, cache))
    r = rng.choice(_rs(m, k, cache))
    order, mul, _ = lib.semidirect_group(m, k, r)
    S = rng.sample(range(order), d)
    # Base: two vertices joined by d darts with voltages S. Side 0 = 0..order-1, side 1 = order..2*order-1.
    n, edges = lib.group_lift(2, [(0, 1, s) for s in S], order, mul)
    if lib.within_diameter(n, edges, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    cache = {}
    best = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    lo, hi = d, None                     # side size lo is known achievable; hi known to fail

    while time.monotonic() < deadline:
        if hi is None:
            N = lo + max(1, lo // 60)
        elif hi - lo > 1:
            N = (lo + hi) // 2
        else:
            N = lo + 1

        result = None
        for _ in range(40):
            if time.monotonic() >= deadline:
                break
            result = _try(N, d, D, rng, cache)
            if result is not None:
                break

        if time.monotonic() >= deadline and result is None:
            break

        if result is not None:
            best = result
            lo = N
        else:
            hi = N

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return lib.haar_graph(d, range(d))
