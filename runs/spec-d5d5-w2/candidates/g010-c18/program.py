import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy:
#   D <= 2 : K_{d,d} (meets the Moore bound for D = 2).
#   D == 3 : incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
#   D >= 4 : a new family. Simple d-regular bipartite graphs on N+N vertices,
#            started from a cyclic (Haar) graph and annealed by double-edge swaps
#            that minimise the number of vertex pairs at distance > D. The order
#            grows as long as annealing reaches zero unreached pairs.
# Every candidate passes lib.is_valid before it replaces the best graph, and the
# K_{d,d} fallback is always available.
# ----------------------------------------------------------------------------


def _cost(n, adj, D):
    """Total number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
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


def _cyclic_start(N, d, rng):
    """Simple d-regular bipartite graph: a in [0,N) joined to N + (a+s) mod N for d distinct shifts s."""
    shifts = rng.sample(range(N), d)
    adj = [[] for _ in range(2 * N)]
    E = []
    S = set()
    for a in range(N):
        for s in shifts:
            b = N + (a + s) % N
            adj[a].append(b)
            adj[b].append(a)
            E.append((a, b))
            S.add((a, b))
    return adj, E, S


def _apply(adj, E, S, i, j, a1, b1, a2, b2):
    """Replace edges (a1,b1), (a2,b2) by (a1,b2), (a2,b1). Keeps all degrees fixed."""
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    adj[a1].append(b2)
    adj[b2].append(a1)
    adj[a2].append(b1)
    adj[b1].append(a2)
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _anneal(N, d, D, rng, deadline):
    """Anneal a simple d-regular bipartite graph on N+N vertices to diameter <= D.

    Returns the edge list (absolute indices) on success, else None.
    """
    n = 2 * N
    adj, E, S = _cyclic_start(N, d, rng)
    cur = _cost(n, adj, D)
    if cur == 0:
        return list(E)
    T0 = 1.0 + 0.02 * cur
    T1 = 0.5
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac
        for _ in range(20):
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
                continue
            _apply(adj, E, S, i, j, a1, b1, a2, b2)
            c = _cost(n, adj, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                if cur == 0:
                    break
            else:
                # revert: remove (a1,b2),(a2,b1), restore (a1,b1),(a2,b2)
                _apply(adj, E, S, i, j, a1, b2, a2, b1)
    return list(E) if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D == 3: projective plane incidence graph of the largest usable order.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 4: grow the per-side order N of a simple d-regular bipartite graph.
    lo = max(d, best[0] // 2)          # largest N known to succeed
    step = max(1, lo // 16)
    while time.monotonic() < deadline:
        N = lo + step
        if 2 * N > moore:
            break
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.2:
            break
        attempt_deadline = now + max(2.0, 0.4 * remaining)
        attempt_deadline = min(attempt_deadline, deadline)
        E = _anneal(N, d, D, rng, attempt_deadline)
        if E is not None:
            consider(2 * N, E)
            lo = N
            step = max(1, lo // 16)
        else:
            if step == 1:
                break
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
