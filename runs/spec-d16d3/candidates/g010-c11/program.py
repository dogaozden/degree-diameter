import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback family: incidence graph of PG(2, q), q the largest prime power <= d-1.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: d-regular bipartite graphs on sides of size s, diameter 3,
# found by annealing over degree-preserving double edge swaps.
#
# Side A is vertices 0..s-1, side B is s..2s-1. nbA[a] and nbB[b] are bitmasks
# of neighbours on the opposite side.
# ----------------------------------------------------------------------------

def _cost3(s, nbA, nbB):
    """Number of ordered (vertex, target) pairs at distance > 3 (zero iff diameter <= 3)."""
    total = 0
    for a in range(s):
        # Same-side A vertices at distance <= 2 (a itself included).
        R2 = 0
        t = nbA[a]
        while t:
            low = t & -t
            R2 |= nbB[low.bit_length() - 1]
            t ^= low
        total += s - R2.bit_count()
        # B vertices at distance <= 3: neighbours of A-vertices at distance <= 2.
        reach = 0
        t = R2
        while t:
            low = t & -t
            reach |= nbA[low.bit_length() - 1]
            t ^= low
        total += s - reach.bit_count()
    # Same-side B pairs at distance <= 2.
    for b in range(s):
        R2 = 0
        t = nbB[b]
        while t:
            low = t & -t
            R2 |= nbA[low.bit_length() - 1]
            t ^= low
        total += s - R2.bit_count()
    return total


def _anneal3(s, d, rng, deadline):
    """Anneal a d-regular bipartite graph on sides of size s toward diameter 3. Returns side-indexed edges or None."""
    S = rng.sample(range(s), d)
    nbA = [0] * s
    nbB = [0] * s
    E = []
    for a in range(s):
        for t in S:
            b = (a + t) % s
            nbA[a] |= 1 << b
            nbB[b] |= 1 << a
            E.append([a, b])
    cost = _cost3(s, nbA, nbB)
    M = len(E)
    T0, T1 = 3.0, 0.2
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (nbA[a1] >> b2) & 1 or (nbA[a2] >> b1) & 1:
            continue
        # Swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). XOR masks are self-inverse.
        mA1 = (1 << b1) | (1 << b2)
        mA2 = (1 << b2) | (1 << b1)
        mB1 = (1 << a1) | (1 << a2)
        mB2 = (1 << a2) | (1 << a1)
        nbA[a1] ^= mA1
        nbA[a2] ^= mA2
        nbB[b1] ^= mB1
        nbB[b2] ^= mB2
        new = _cost3(s, nbA, nbB)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            nbA[a1] ^= mA1
            nbA[a2] ^= mA2
            nbB[b1] ^= mB1
            nbB[b2] ^= mB2

    if cost == 0:
        return E
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3 and d >= 3:
        moore = lib._moore_bound(d, 3)
        s = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline and 2 * s <= moore:
            remaining = deadline - time.monotonic()
            attempt_deadline = min(deadline, time.monotonic() + max(5.0, 0.5 * remaining))
            E = _anneal3(s, d, rng, attempt_deadline)
            if E is None:
                continue
            edges = [(a, s + b) for a, b in E]
            consider(2 * s, edges)
            s += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
