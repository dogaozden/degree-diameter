import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Different family from the parent: bipartite graphs with no imposed group
# symmetry. We start from a random d-regular bipartite graph on n + n vertices
# and anneal with double-edge switches (which keep degrees and bipartiteness)
# to drive the number of vertex pairs at distance > D to zero. The order n is
# searched by bisection, so the best feasible size is found and then pushed up.
# ----------------------------------------------------------------------------


def _set_edge(adj, eset, E, i, new):
    """Replace edge number i by `new` = (a, b) with a in A (low ids) and b in B."""
    a, b = E[i]
    adj[a].remove(b)
    adj[b].remove(a)
    eset.discard((a, b))
    a2, b2 = new
    adj[a2].append(b2)
    adj[b2].append(a2)
    eset.add((a2, b2))
    E[i] = (a2, b2)


def _random_regular(h, d, rng):
    """Random d-regular bipartite graph with sides 0..h-1 and h..2h-1, or None."""
    adj = [[] for _ in range(2 * h)]
    E = []
    eset = set()
    for _ in range(d):
        ok = False
        for _attempt in range(2000):
            perm = list(range(h))
            rng.shuffle(perm)
            if all((a, h + perm[a]) not in eset for a in range(h)):
                ok = True
                break
        if not ok:
            return None
        for a in range(h):
            b = h + perm[a]
            E.append((a, b))
            eset.add((a, b))
            adj[a].append(b)
            adj[b].append(a)
    return adj, E, eset


def _bad(n, adj, D):
    """Number of ordered vertex pairs at distance > D (unreached pairs), via bitsets."""
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


def _anneal(n, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on n + n vertices toward diameter <= D.

    Returns the edge list (pairs (a, b) with a < n/2 <= b) on success, else None.
    """
    h = n // 2
    if h < d:
        return None
    init = _random_regular(h, d, rng)
    if init is None:
        return None
    adj, E, eset = init
    m = len(E)
    cost = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.1
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        oi, oj = E[i], E[j]
        _set_edge(adj, eset, E, i, (a1, b2))
        _set_edge(adj, eset, E, j, (a2, b1))
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _set_edge(adj, eset, E, i, oi)
            _set_edge(adj, eset, E, j, oj)
    if cost == 0:
        return list(E)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def take(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if d == 2:
        # Even cycle C_{2D}: bipartite, max degree 2, diameter D.
        L = 2 * D
        take(L, [(i, (i + 1) % L) for i in range(L)])
        return best

    moore = lib.moore_bound(d, D)

    if D == 3 and lib.is_prime_power(d - 1):
        # Projective plane incidence graph is extremal for D = 3.
        take(*lib.projective_plane_incidence(d - 1))
        return best

    rng = random.Random(seed * 1000003 + d * 101 + D)

    def clamp_even(x):
        x = max(2 * d, min(x, moore))
        return x - (x % 2)

    n = clamp_even(int(0.5 * moore))
    lo_ok = None   # largest order found feasible by annealing
    hi_bad = None  # smallest order where annealing failed

    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        slice_len = max(3.0, 0.4 * remaining)
        slice_end = min(deadline, now + slice_len)

        edges = _anneal(n, d, D, rng, slice_end)
        success = edges is not None and take(n, edges)

        if success:
            if lo_ok is None or n > lo_ok:
                lo_ok = n
        else:
            if hi_bad is None or n < hi_bad:
                hi_bad = n

        if lo_ok is not None and hi_bad is not None:
            if hi_bad - lo_ok <= 2:
                # Bracket is tight; try once more just above the feasible order
                # with a fresh random start, then stop bisecting.
                nxt = lo_ok + 2
                if nxt >= hi_bad or nxt > moore:
                    break
            else:
                nxt = (lo_ok + hi_bad) // 2
                nxt -= nxt % 2
                if nxt <= lo_ok:
                    nxt = lo_ok + 2
                if nxt >= hi_bad:
                    break
        elif success:
            nxt = n + 4
        else:
            nxt = n - 8

        if nxt < 2 * d or nxt > moore:
            nxt = clamp_even(nxt)
            if lo_ok is not None and nxt <= lo_ok:
                break
        n = nxt

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
