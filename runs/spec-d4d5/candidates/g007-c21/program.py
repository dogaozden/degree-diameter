import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap algebraic candidates (diameter 3 families).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for q = d - 2 when that is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, KeyError, IndexError):
        return None


# ----------------------------------------------------------------------------
# New family: bipartite graphs with fixed sides A = {0..N-1}, B = {N..2N-1},
# every vertex of degree d, found by edge-switch annealing. Each move swaps the
# partners of two edges, which keeps every degree fixed. The objective is the
# number of ordered vertex pairs at distance > D, computed with bitset balls.
# A zero objective means the graph is valid. The search starts from a Haar
# graph (a circulant bipartite graph), so the start is already d-regular.
# ----------------------------------------------------------------------------

def _cost(N, D, E):
    """Ordered pairs not within distance D (zero means diameter <= D)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _search(d, D, N, rng, deadline):
    """Anneal an N+N bipartite d-regular graph toward diameter <= D; return edge list or None."""
    S = rng.sample(range(N), d)
    Eset = {(i, (i + s) % N) for i in range(N) for s in S}
    E = list(Eset)
    c = _cost(N, D, E)
    if c == 0:
        return E

    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    T0, T_end = 2.0, 0.08
    while c > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = T0 * (T_end / T0) ** min(1.0, frac)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = _cost(N, D, E)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add((a1, b2))
            Eset.add((a2, b1))
            c = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    if deadline < start + 0.5:
        deadline = start + 0.5 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Edge-switch annealing for larger diameters, starting from the best known size.
    if D >= 4:
        N = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline:
            now = time.monotonic()
            budget = max(1.0, 0.25 * (deadline - now))
            sub_deadline = min(deadline, now + budget)
            E = _search(d, D, N, rng, sub_deadline)
            if E is not None:
                n, e = 2 * N, [(a, N + b) for a, b in E]
                consider(n, e)
                N += 1
            # On failure the same N is retried with a fresh random start.

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
