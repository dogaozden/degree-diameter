import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D >= 3 (bold change): random-like d-regular bipartite
# graphs found by simulated annealing, instead of group-structured lifts.
#
# Side A = {0..N-1}, side B = {N..2N-1}. The graph is the union of d perfect
# matchings (layers) P[l]: x in A is joined to N + P[l][x]. Each layer starts as
# a shifted cyclic matching (x -> x + l mod N), so all edges are distinct.
# Moves swap the targets of two A-vertices inside one layer, which keeps every
# vertex at degree exactly d and every edge distinct. The cost is the number of
# ordered vertex pairs at distance > D, computed with big-integer bitsets.
# Orders are grown one step at a time while annealing still reaches cost 0.
#
# Safe fallback: K_{d,d} (diameter 2). D = 3 also tries the projective plane
# incidence graph first. Every returned graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------


def _cost(adj, M, D):
    """Ordered pairs (v, w) with dist(v, w) > D. Zero means diameter <= D."""
    reach = [1 << v for v in range(M)]
    for _ in range(D):
        nxt = [0] * M
        for v in range(M):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(M - r.bit_count() for r in reach)


def _swap(adj, P, l, x, y, N):
    """Exchange the targets of A-vertices x and y in layer l (unconditional).

    Applying the same call again undoes the move.
    """
    a = P[l][x]
    b = P[l][y]
    adj[x].discard(N + a)
    adj[N + a].discard(x)
    adj[y].discard(N + b)
    adj[N + b].discard(y)
    adj[x].add(N + b)
    adj[N + b].add(x)
    adj[y].add(N + a)
    adj[N + a].add(y)
    P[l][x] = b
    P[l][y] = a


def _anneal(N, d, D, rng, deadline, T0=2.0, T1=0.05):
    """Anneal a d-regular bipartite graph on 2N vertices to diameter <= D.

    Returns the adjacency sets (vertices 0..2N-1) on success, else None.
    """
    M = 2 * N
    P = [[(x + l) % N for x in range(N)] for l in range(d)]
    adj = [set() for _ in range(M)]
    for l in range(d):
        for x in range(N):
            y = N + P[l][x]
            adj[x].add(y)
            adj[y].add(x)

    cur = _cost(adj, M, D)
    if cur == 0:
        return adj
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
        l = rng.randrange(d)
        x, y = rng.sample(range(N), 2)
        a = P[l][x]
        b = P[l][y]
        if (N + b) in adj[x] or (N + a) in adj[y]:
            continue
        _swap(adj, P, l, x, y, N)
        new = _cost(adj, M, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _swap(adj, P, l, x, y, N)  # undo
    if cur == 0:
        return adj
    return None


def _edges_from(adj, N):
    return [(x, y) for x in range(N) for y in adj[x]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 1.0)
    deadline = start + total

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    # Already at the Moore bound (e.g. d=3, D=3 gives 14): nothing to gain.
    if best[0] >= lib._moore_bound(d, D):
        return best

    # D = 3: projective plane incidence graph when d-1 is a prime power or
    # the largest prime power below it otherwise.
    if D == 3:
        try:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    n2, e2 = lib.projective_plane_incidence(q)
                    consider(n2, e2)
                    break
        except Exception:
            pass

    # Main phase: grow the order N of a d-regular bipartite graph on 2N vertices.
    try:
        if d >= 2:
            rng = random.Random(seed)
            N = max(d, 2, best[0] // 2)
            step = max(1, N // 16)
            while time.monotonic() < deadline - 0.2:
                now = time.monotonic()
                slice_end = min(deadline, now + max(1.0, 0.2 * total))
                adj = _anneal(N, d, D, rng, slice_end)
                if adj is not None:
                    consider(2 * N, _edges_from(adj, N))
                    N += step
                    step = max(1, N // 16)
                else:
                    # Failure at this order: retry it with a fresh random walk,
                    # growing again by single steps only.
                    step = 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
