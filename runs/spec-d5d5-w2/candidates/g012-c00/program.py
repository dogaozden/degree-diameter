import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Different family from the parent: a time-annealed edge-switch search over
# simple bipartite graphs with a fixed bipartition (A = 0..N-1, B = N..2N-1).
# The objective is the number of vertex pairs at distance > D, computed with
# integer bitsets. Edge switches keep every degree fixed, so degree <= d holds
# throughout. The best verified graph is always kept; K_{d,d} (diameter 2) is
# the fallback. For D = 3 the projective-plane incidence graph is used when
# d-1 is a prime power, since it meets the Moore bound.
# ----------------------------------------------------------------------------


def _cost(n, adj, D):
    """Number of ordered (source, target) pairs at distance > D (0 means valid)."""
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


def _repl(lst, old, new):
    lst[lst.index(old)] = new


def _switch(E, S, adj, i, j):
    """Replace edges (a1,v1),(a2,v2) with (a1,v2),(a2,v1). Calling it again on
    the same indices undoes the move."""
    a1, v1 = E[i]
    a2, v2 = E[j]
    S.discard((a1, v1))
    S.discard((a2, v2))
    S.add((a1, v2))
    S.add((a2, v1))
    E[i] = (a1, v2)
    E[j] = (a2, v1)
    _repl(adj[a1], v1, v2)
    _repl(adj[v1], a1, a2)
    _repl(adj[a2], v2, v1)
    _repl(adj[v2], a2, a1)


def _search(N, d, D, rng, t0, deadline):
    """Annealed edge-switch search for a valid bipartite graph on 2N vertices.
    Returns an edge list or None."""
    n = 2 * N
    S = set()
    E = []
    adj = [[] for _ in range(n)]
    for _ in range(d):
        perm = list(range(N))
        rng.shuffle(perm)
        for a in range(N):
            v = N + perm[a]
            if (a, v) not in S:
                S.add((a, v))
                E.append((a, v))
                adj[a].append(v)
                adj[v].append(a)
    M = len(E)
    if M < 2:
        return None
    cur = _cost(n, adj, D)
    T0, T1 = 2.0, 0.05
    span = max(1e-6, deadline - t0)
    step = 0
    while cur > 0:
        step += 1
        if (step & 15) == 0:
            now = time.monotonic()
            if now > deadline:
                break
            frac = min(1.0, (now - t0) / span)
        else:
            frac = min(1.0, (time.monotonic() - t0) / span)
        T = T0 * (T1 / T0) ** frac

        i = j = -1
        for _ in range(20):
            i = rng.randrange(M)
            j = rng.randrange(M)
            if i == j:
                continue
            a1, v1 = E[i]
            a2, v2 = E[j]
            if a1 == a2 or v1 == v2 or (a1, v2) in S or (a2, v1) in S:
                continue
            break
        else:
            continue

        _switch(E, S, adj, i, j)
        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _switch(E, S, adj, i, j)

    if cur == 0:
        return list(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed * 1000003 + d * 31 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    # Structured D = 3 baseline: projective plane incidence graph.
    if D == 3:
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            n_pg, e_pg = lib.projective_plane_incidence(q)
            consider(n_pg, e_pg)

    try:
        bestN = best[0] // 2
        frac_step = 0.04
        while time.monotonic() < deadline:
            step = max(1, int(bestN * frac_step))
            N = bestN + step
            if 2 * N > moore:
                break
            now = time.monotonic()
            remaining = deadline - now
            slice_end = min(deadline, now + max(1.5, 0.3 * remaining))
            E = _search(N, d, D, rng, now, slice_end)
            ok = False
            if E is not None and lib.is_valid(2 * N, E, d, D):
                best = (2 * N, list(E))
                bestN = N
                ok = True
            if not ok:
                frac_step /= 2.0
                if max(1, int(bestN * frac_step)) == 1 and step == 1:
                    break
    except Exception:
        pass  # keep the best verified graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
