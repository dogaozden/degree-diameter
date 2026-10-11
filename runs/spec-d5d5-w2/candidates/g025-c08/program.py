import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (changed from the parent):
#   * D = 3: projective-plane incidence graph (meets the Moore bound when d-1 is a
#     prime power, otherwise a valid baseline).
#   * D >= 4: bi-Cayley lifts A_x ~ B_{x*g} (g in S) over semidirect products
#     Z_m x|_r Z_k of order N, giving 2N vertices. Connection sets are found by
#     simulated annealing on the number of unreached (source, target) pairs,
#     instead of the parent's plateau hill-climb. Orders are swept upward from a
#     target above the current record, so every accepted graph beats the last.
#   * Fallback: K_{d,d} (diameter 2), and a cycle C_{2D} for d = 2. Every graph
#     is checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_CACHE = {}


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    if len(_CACHE) >= 24:
        _CACHE.clear()
    _CACHE[key] = (order, T, invs)
    return _CACHE[key]


def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_0 and B_0.

    Left translations are automorphisms, so checking these two sources suffices.
    Returns 0 exactly when the bi-Cayley graph has diameter <= D.
    """
    Sinv = [invs[g] for g in S]
    full = 2 * N
    total = 0
    for src in (0, N):
        seen = bytearray(full)
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += full - count
    return total


def _anneal(N, T, invs, d, D, rng, deadline):
    """Simulated annealing over connection sets S (identity fixed as one element)."""
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    it = 0
    cap = 40000
    while cur > 0 and it < cap and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        temp = max(0.05, 1.5 * (1.0 - it / cap))
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d <= 1:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best

    rng = random.Random(seed)
    # Start the sweep near the record band, not at the trivial baseline.
    N = max(best[0] // 2 + 1, moore // 4)
    per_N = max(1.0, 0.08 * budget)

    while time.monotonic() < deadline and 2 * N <= moore:
        groups = _groups(N)
        rng.shuffle(groups)
        now = time.monotonic()
        n_deadline = min(deadline, now + per_N)
        slice_t = (n_deadline - now) / max(1, len(groups))
        found = None
        for m, k, r in groups:
            if time.monotonic() >= n_deadline:
                break
            order, T, invs = _tables(m, k, r)
            gd = min(n_deadline, time.monotonic() + slice_t)
            S = _anneal(N, T, invs, d, D, rng, gd)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
