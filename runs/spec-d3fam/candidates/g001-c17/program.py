import random
import time
import lib


def _valid(n, edges, d, D):
    try:
        return lib.is_valid(n, edges, d, D)
    except Exception:
        return False


def _best_structured(d, D):
    """Largest valid structured construction for this case, or None."""
    if D != 3:
        return None
    makers = []
    # Araujo-Pardo & Lopez record: PG(2,q) plus 8 vertices, degree q+2 = d, q = d-2.
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        makers.append(lambda q=q: lib.araujo_lopez_graph(q))
    # Plain projective plane incidence graphs: degree q+1, q = d-1 or d-2.
    for q in (d - 1, d - 2):
        if q >= 2 and lib.is_prime_power(q):
            makers.append(lambda q=q: lib.projective_plane_incidence(q))
    best = None
    for make in makers:
        try:
            n, edges = make()
        except Exception:
            continue
        if _valid(n, edges, d, D) and (best is None or n > best[0]):
            best = (n, edges)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    structured = _best_structured(d, D)
    if structured is not None:
        return structured

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
