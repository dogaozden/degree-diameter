import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family: random d-regular bipartite graphs found by edge-swap annealing.
#
# Start from a Haar graph on Z_m with d distinct shifts (automatically simple,
# d-regular, bipartite). Degree-preserving 2-switches randomize it, and the
# cost is the number of vertex pairs at distance > D. Growing m by doubling and
# then bisection gives the largest m for which a zero-cost graph is found.
# ----------------------------------------------------------------------------

def _bad_cost(m, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph with edges E (A-index, B-index)."""
    n = 2 * m
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _search(d, D, m, rng, deadline):
    """Anneal a d-regular bipartite graph on m+m vertices to diameter <= D. Return edge list (a, b) or None."""
    shifts = rng.sample(range(m), d)
    E = [(i, (i + s) % m) for s in shifts for i in range(m)]
    Sset = set(E)
    cost = _bad_cost(m, E, D)
    if cost == 0:
        return E
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 0.15 + 1.0 * (1.0 - frac)

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in Sset or n2 in Sset:
            continue

        E[i] = n1
        E[j] = n2
        c2 = _bad_cost(m, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            Sset.discard((a1, b1))
            Sset.discard((a2, b2))
            Sset.add(n1)
            Sset.add(n2)
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E


def _edges_from(m, E):
    """Convert (a, b) pairs into graph edges with B-vertices offset by m."""
    return [(a, m + b) for a, b in E]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Projective-plane incidence graph is diameter 3 and degree <= d (D >= 3).
    if D >= 3:
        q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)

    # Random bipartite search: doubling, then bisection on the side size m.
    lo = d          # K_{d,d} (side size d) is feasible
    hi = None       # smallest side size known infeasible
    while time.monotonic() < deadline:
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2

        now = time.monotonic()
        att = min(deadline, now + max(1.0, 0.3 * (deadline - now)))
        E = _search(d, D, m, rng, att)
        if E is not None:
            lo = m
            consider(2 * m, _edges_from(m, E))
        else:
            hi = m

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
