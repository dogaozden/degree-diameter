import random
import time
import lib


def _largest_prime_power_at_most(x):
    q = x
    while q >= 2:
        if lib.is_prime_power(q):
            return q
        q -= 1
    return None


def _safe(fn):
    try:
        return fn()
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    # Safe fallback: complete bipartite K_{d,d}, always valid for D >= 1.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, edges = g
        if n > best_n and lib.is_valid(n, edges, d, D):
            best, best_n = (n, edges), n

    if D == 3 and d >= 3:
        # Bold change: stop searching blindly. Use algebraic constructions.
        # (a) Araujo-Pardo / Lopez record family, degree q+2 = d, order 2(q^2+q+5).
        #     Valid when q = d-2 is a prime power >= 3 (d = 11, 13, 15 are targets).
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            consider(_safe(lambda: lib.araujo_lopez_graph(q)))

        # (b) Projective plane incidence PG(2, q), degree q+1 <= d, with q the
        #     largest prime power not exceeding d-1.
        q2 = _largest_prime_power_at_most(d - 1)
        if q2 is not None and q2 >= 2:
            consider(_safe(lambda: lib.projective_plane_incidence(q2)))

    # Structured candidates found: done unless time permits a heuristic search
    # for a larger graph. Only search generically if nothing beat K_{d,d}.
    if best_n > d + d:
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
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(found)
            misses = 0
        else:
            misses += 1
        m += 1
    return best
