import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Unstructured search: bipartite d-regular graphs on N + N vertices, improved
# by edge switches under simulated annealing. The cost is the number of ordered
# vertex pairs farther apart than D, computed with bitmask balls. This replaces
# the group-lift search with a different construction family.
# ----------------------------------------------------------------------------

T_START = 3.0
T_END = 0.05


def _cost(n, adj, D):
    """Number of ordered vertex pairs at distance > D. Zero iff diameter <= D."""
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


def _rm(lst, x):
    i = lst.index(x)
    lst[i] = lst[-1]
    lst.pop()


def _switch(E, eset, adj, N, i, j):
    """Replace edges (a,b), (c,e) by (a,e), (c,b). Self-inverse when applied to the new pair."""
    a, b = E[i]
    c, e = E[j]
    _rm(adj[a], N + b)
    _rm(adj[N + b], a)
    _rm(adj[c], N + e)
    _rm(adj[N + e], c)
    adj[a].append(N + e)
    adj[N + e].append(a)
    adj[c].append(N + b)
    adj[N + b].append(c)
    eset.discard(a * N + b)
    eset.discard(c * N + e)
    eset.add(a * N + e)
    eset.add(c * N + b)
    E[i] = (a, e)
    E[j] = (c, b)


def _anneal(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on N + N vertices to diameter <= D.

    Returns the edge list as (a, b) pairs with a, b in 0..N-1, or None on timeout.
    """
    # Start from a Haar-type graph: a ~ b when b - a lies in a random set of d shifts.
    shifts = rng.sample(range(N), d)
    E = [(a, (a + s) % N) for a in range(N) for s in shifts]
    eset = {a * N + b for a, b in E}
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    cur = _cost(n, adj, D)
    m = len(E)

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = T_START * (T_END / T_START) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if a * N + e in eset or c * N + b in eset:
            continue

        _switch(E, eset, adj, N, i, j)
        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _switch(E, eset, adj, N, i, j)  # undo

    return E


def _pg_candidate(d):
    """Incidence graph of PG(2, d-1): Moore-optimal for D = 3 when d-1 is a prime power."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 <= D and is always valid here.
    best = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            return pg

    max_n = moore // 2  # each side has N vertices, so 2N <= moore
    best_n = d
    target = max(best_n + 1, int(0.4 * max_n))

    while time.monotonic() < deadline and target <= max_n:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        seg = min(remaining, max(1.0, 0.2 * budget))
        E = _anneal(target, d, D, rng, now + seg)
        if E is not None:
            n = 2 * target
            edges = [(a, target + b) for a, b in E]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            best_n = target
            target = best_n + max(1, best_n // 25)
        else:
            gap = target - best_n
            if gap > 1:
                target = best_n + max(1, gap // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    return best
