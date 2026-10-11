import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: random-start bipartite regular graphs improved by
# double-edge-swap simulated annealing. The objective is the number of ordered
# vertex pairs at distance > D, computed with big-int reachability bitsets.
# Every intermediate graph is d-regular and bipartite by construction.
# The start is a bi-Cayley (Haar) circulant, which is then perturbed away from
# the cyclic class by swaps.
# ----------------------------------------------------------------------------

T_START = 2.0
T_END = 0.05


def _bad(n2, adj, D):
    """Number of ordered pairs (v, w) with dist(v, w) > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n2)]
    for _ in range(D):
        new = [0] * n2
        for v in range(n2):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n2 - r.bit_count() for r in reach)


def _swap(adj, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Left vertices a*, right vertices b*."""
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    adj[a1].append(b2)
    adj[b2].append(a1)
    adj[a2].append(b1)
    adj[b1].append(a2)


def _anneal(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with N + N vertices toward diameter <= D.

    Returns (n, edges) on success, or None if the deadline passes first.
    """
    n2 = 2 * N
    shifts = rng.sample(range(N), d)
    E = [[i, N + (i + s) % N] for i in range(N) for s in shifts]
    adj = [[] for _ in range(n2)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)

    cost = _bad(n2, adj, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    m = len(E)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - start) / span)
        T = T_START * (T_END / T_START) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        # New edges (a1,b2) and (a2,b1) must not already exist.
        if b2 in adj[a1] or b1 in adj[a2]:
            continue

        _swap(adj, a1, b1, a2, b2)
        c2 = _bad(n2, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            _swap(adj, a1, b2, a2, b1)  # undo

    return n2, [(a, b) for a, b in E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph meets the Moore bound when d-1 is a prime power.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n3, e3 = lib.projective_plane_incidence(q)
                consider(n3, e3)
                break

    if best[0] >= moore:
        return best

    rng = random.Random(seed * 7919 + d * 31 + D)

    # Ladder over the per-side size N: try to grow while annealing succeeds.
    N = max(d, best[0] // 2 + 1, moore // 5)
    fails = 0
    while time.monotonic() < deadline and N <= moore // 2 and fails < 6:
        now = time.monotonic()
        remaining = deadline - now
        att_deadline = min(deadline, now + max(1.0, 0.6 * remaining))
        res = _anneal(N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            N = max(d, N - 6)
            continue
        consider(res[0], res[1])
        N = max(N + 2, best[0] // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
