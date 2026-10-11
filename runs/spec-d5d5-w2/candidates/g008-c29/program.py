import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3: projective-plane incidence graph (meets the Moore bound when d-1 is a
# prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Raw bipartite search: d-regular bipartite graphs on 2h vertices (A = 0..h-1,
# B = h..2h-1) are annealed toward diameter <= D using degree-preserving double
# edge swaps. Cost = number of ordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of ordered vertex pairs at distance > D, via bitmask balls."""
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
    return sum(n - r.bit_count() for r in reach)


def _swap(E, S, adj, i, j):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1) in place. Calling it again on the same
    indices undoes the swap."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    E[i] = (a1, b2)
    E[j] = (a2, b1)
    adj[a1].remove(b1)
    adj[a1].append(b2)
    adj[b1].remove(a1)
    adj[b1].append(a2)
    adj[a2].remove(b2)
    adj[a2].append(b1)
    adj[b2].remove(a2)
    adj[b2].append(a1)


def _run(d, D, h, rng, deadline):
    """Anneal a d-regular bipartite graph with 2h vertices toward diameter D.
    Returns the edge list (A id, B id) if diameter <= D is reached, else None."""
    n = 2 * h
    E = [(i, h + (i + s) % h) for s in range(d) for i in range(h)]
    S = set(E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    m = len(E)

    # Randomize with degree-preserving swaps (no cost evaluation).
    for _ in range(3 * m):
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        _swap(E, S, adj, i, j)

    cost = _bad(n, adj, D)
    if cost == 0:
        return E

    T0, T1 = 3.0, 0.2
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    step = 0
    while True:
        if (step & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        step += 1
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        _swap(E, S, adj, i, j)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return E
        else:
            _swap(E, S, adj, i, j)
    return None


def _search(d, D, moore, best, rng, deadline):
    """Binary search for the largest side size h that the annealer can realise.
    lo is always a known-valid side size (h = d gives K_{d,d})."""
    lo = d
    hi = moore // 2
    while lo < hi:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        mid = (lo + hi + 1) // 2
        slice_end = now + max(2.0, 0.4 * remaining)
        res = _run(d, D, mid, rng, min(deadline, slice_end))
        ok = False
        if res is not None:
            n, e = 2 * mid, [(a, b) for a, b in res]
            if lib.is_valid(n, e, d, D):
                ok = True
                if n > best[0]:
                    best = (n, e)
        if ok:
            lo = mid
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    try:
        if D == 3:
            pg = _best_pg(d)
            if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
                best = pg
            if best[0] >= moore:
                return best
        best = _search(d, D, moore, best, rng, deadline)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
