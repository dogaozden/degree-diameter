import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3: incidence graph of PG(2, q), q the largest prime power with q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# D >= 4: annealed search over d-regular bipartite graphs with N vertices per
# side (total 2N). Start from a circulant, then do degree-preserving 2-switches
# (a1-b1, a2-b2 -> a1-b2, a2-b1) that minimise the number of vertex pairs at
# distance more than D. A zero-cost state is a valid graph. The side size N is
# searched by growth then bisection.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _rep(lst, old, new):
    lst[lst.index(old)] = new


def _apply(E, adj, M, N, i, j):
    """Switch edges i and j: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Involution when repeated."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    _rep(adj[a1], N + b1, N + b2)
    _rep(adj[N + b1], a1, a2)
    _rep(adj[a2], N + b2, N + b1)
    _rep(adj[N + b2], a2, a1)
    M[a1 * N + b1] = 0
    M[a2 * N + b2] = 0
    M[a1 * N + b2] = 1
    M[a2 * N + b1] = 1
    E[i] = [a1, b2]
    E[j] = [a2, b1]


def _sa(N, d, D, deadline, rng):
    """Try to find a d-regular bipartite graph on N+N vertices with diameter <= D.

    Returns the list of edges [a, b] (side indices 0..N-1), or None on timeout.
    """
    if N < d:
        return None
    n = 2 * N
    shifts = rng.sample(range(N), d)
    E = [[a, (a + s) % N] for a in range(N) for s in shifts]
    M = bytearray(N * N)
    adj = [[] for _ in range(n)]
    for a, b in E:
        M[a * N + b] = 1
        adj[a].append(N + b)
        adj[N + b].append(a)

    cost = _cost(n, adj, D)
    if cost == 0:
        return E

    m = len(E)
    T0 = 1.0 + 0.05 * cost
    T = T0
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    frac = 0.0
    it = 0
    while True:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
            T = T0 * (1.0 - frac) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if M[a1 * N + b2] or M[a2 * N + b1]:
            continue
        _apply(E, adj, M, N, i, j)
        new = _cost(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            if cost == 0:
                break
        else:
            _apply(E, adj, M, N, i, j)

    if cost == 0:
        return E
    return None


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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best

    moore = lib.moore_bound(d, D)
    half_moore = moore // 2

    try:
        lo = d          # K_{d,d} is a known success
        hi = None       # smallest known failing side size
        while time.monotonic() < deadline:
            if hi is None:
                mid = int(lo * 1.25) + 1
                if mid > half_moore:
                    mid = half_moore
            else:
                mid = (lo + hi) // 2
            if mid <= lo:
                break
            if hi is not None and mid >= hi:
                mid = (lo + hi) // 2
                if mid <= lo:
                    break

            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            slice_t = min(remaining, max(1.0, 0.35 * remaining))
            E = _sa(mid, d, D, now + slice_t, rng)
            if E is not None:
                lo = mid
                consider(2 * mid, [(a, mid + b) for a, b in E])
            else:
                hi = mid
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
