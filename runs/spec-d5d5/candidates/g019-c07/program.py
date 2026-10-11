import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Bi-Cayley lifts over an arbitrary finite group given by a multiplication table.
#
# A bi-Cayley graph on a group G with connection set S (|S| = d) has vertices
# A_x, B_x (x in G) and edges A_x ~ B_{x g} for g in S. Left translation is an
# automorphism, so distances only need checking from A_0 and B_0.
#
# Groups are drawn from two families:
#   * semidirect products Z_m x|_r Z_k (cyclic-normal, as in lib.semidirect_group)
#   * NON-CYCLIC abelian groups Z_a x Z_b with gcd(a, b) > 1 (new family here)
# Both are expressed through the same (order, T, invs) table interface.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12        # groups tried per order N before choosing another N
CLIMB_ITERS = 1500     # annealing steps per group
_TABLE_CACHE = {}
_CACHE_LIMIT = 40


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_specs(N):
    """Descriptors of groups of order N: semidirect products and non-cyclic abelian groups."""
    specs = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(("semi", m, k, r))
    for a in range(2, math.isqrt(N) + 1):
        if N % a == 0:
            b = N // a
            if math.gcd(a, b) > 1:  # gcd 1 would be cyclic, already covered
                specs.append(("ab", a, b))
    return specs


def _table(spec):
    """Cached (order, T, invs) with T[x][g] = x*g and invs[g] = g^-1. Identity is element 0."""
    hit = _TABLE_CACHE.get(spec)
    if hit is not None:
        return hit
    if spec[0] == "semi":
        _, m, k, r = spec
        order, mul, _ = lib.semidirect_group(m, k, r)
    else:
        _, a, b = spec
        order = a * b

        def mul(x, y, a=a, b=b):
            x1, x2 = divmod(x, b)
            y1, y2 = divmod(y, b)
            return ((x1 + y1) % a) * b + (x2 + y2) % b

    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [T[g].index(0) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= _CACHE_LIMIT:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[spec] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of vertices not within distance D of A_0 or B_0 (summed over both sources)."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S (identity fixed as one element, WLOG).

    Returns a valid S (zero unreached pairs) or None.
    """
    if N - 1 < d - 1 or d < 2:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 3.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0:
            break
        if (step & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bi-Cayley search: look for a valid order N with 2N > current best,
    # trying random groups of that order from both families.
    lo = best[0] // 2 + 1
    while best[0] < moore and time.monotonic() < deadline:
        span = max(3, lo // 25)
        N = lo + rng.randrange(span)
        if 2 * N > moore:
            break
        specs = _group_specs(N)
        rng.shuffle(specs)
        found = None
        for spec in specs[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            order, T, invs = _table(spec)
            S = _climb(order, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                found = (order, T, S)
                break
        if found is None:
            continue
        order, T, S = found
        edges = [(x, order + T[x][g]) for x in range(order) for g in S]
        consider(2 * order, edges)
        lo = best[0] // 2 + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
