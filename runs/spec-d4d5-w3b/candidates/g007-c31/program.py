import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Random bi-regular search.
#
# Instead of structured lifts, this searches directly over d-regular bipartite
# graphs on sides A = {0..s-1} and B = {s..2s-1}. The start point is a Haar
# (bi-circulant) graph with random shifts. Moves are edge switches
# (a1-b1, a2-b2) -> (a1-b2, a2-b1), which keep every degree equal to d and
# keep the graph bipartite and simple. The cost is the number of vertex pairs
# at distance greater than D, and the walk is a simulated anneal on that cost.
# ----------------------------------------------------------------------------

def _bad_pairs_adj(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _cost(s, nb, D):
    """Bad-pair cost of the bipartite graph given by nb[a] = list of B-indices adjacent to A-vertex a."""
    n = 2 * s
    adj = [[] for _ in range(n)]
    for a in range(s):
        for b in nb[a]:
            adj[a].append(s + b)
            adj[s + b].append(a)
    return _bad_pairs_adj(n, adj, D)


def _search(s, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph on 2s vertices toward diameter <= D; returns nb or None."""
    if s < d:
        return None
    shifts = rng.sample(range(s), d)
    nb = [[(a + t) % s for t in shifts] for a in range(s)]
    cost = _cost(s, nb, D)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            return None
        a1 = rng.randrange(s)
        a2 = rng.randrange(s)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = nb[a1][i]
        b2 = nb[a2][j]
        if b1 == b2 or b2 in nb[a1] or b1 in nb[a2]:
            continue
        nb[a1][i] = b2
        nb[a2][j] = b1
        c2 = _cost(s, nb, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            nb[a1][i] = b1
            nb[a2][j] = b2
    return nb


def _edges_from_nb(s, nb):
    return [(a, s + b) for a in range(s) for b in nb[a]]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5 * time_limit, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, always valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    # Projective plane incidence graph when d-1 is a prime power (diameter 3).
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        try:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
        except Exception:
            pass

    # Random bi-regular search: try successively larger side sizes s (order 2s),
    # starting just above the current best. Stop at the first failure or at the Moore bound.
    moore = lib.moore_bound(d, D)
    s = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * s <= moore:
        nb = _search(s, d, D, deadline, rng)
        if nb is None:
            break
        n_new = 2 * s
        e_new = _edges_from_nb(s, nb)
        if not lib.is_valid(n_new, e_new, d, D):
            break
        best_n, best_e = n_new, e_new
        s += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
