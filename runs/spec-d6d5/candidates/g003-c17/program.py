import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family: random-start bipartite Haar graphs repaired by double-edge switches.
#
# Each side has N vertices and the graph is d-regular. The start is the Haar
# graph of Z_N with d distinct shifts, which is simple and bipartite. Moves are
# double-edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep the
# degrees and the bipartition. Simulated annealing minimises the number of
# vertex pairs at distance > D. The search raises N as long as it succeeds.
# ----------------------------------------------------------------------------


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
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


def _replace(adj, v, old, new):
    lst = adj[v]
    lst[lst.index(old)] = new


def _anneal(N, d, D, rng, end):
    """Anneal a d-regular bipartite graph with N+N vertices until diameter <= D or time `end`.

    Returns (cost, E) where E is a list of [a, b] edges (a in 0..N-1, b in N..2N-1).
    """
    n = 2 * N
    shifts = rng.sample(range(N), d)
    adj = [[] for _ in range(n)]
    E = []
    for a in range(N):
        for s in shifts:
            b = N + (a + s) % N
            E.append([a, b])
            adj[a].append(b)
            adj[b].append(a)
    eset = {(a, b) for a, b in E}
    M = len(E)
    cost = _bad_pairs(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, end - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - t0) / span
        T = 0.05 ** frac  # temperature decays from 1.0 to 0.05 over the attempt

        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue

        _replace(adj, a1, b1, b2)
        _replace(adj, b1, a1, a2)
        _replace(adj, a2, b2, b1)
        _replace(adj, b2, a2, a1)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            _replace(adj, a1, b2, b1)
            _replace(adj, b1, a2, a1)
            _replace(adj, a2, b1, b2)
            _replace(adj, b2, a1, a2)
    return cost, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best_n = int(n0)
    best_e = [(int(u), int(v)) for u, v in e0]

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n = n
            best_e = [(int(u), int(v)) for u, v in e]

    # Exact optimal graph for D = 3 when d - 1 is a prime power.
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
    if best_n >= moore:
        return best_n, best_e

    # Random-start bipartite search with growing side size.
    max_N = min(max(d, moore // 2), 1500)
    N = min(max_N, max(d, best_n // 2))
    lo, hi = 0, None
    budget_per_attempt = max(3.0, budget / 6.0)

    while time.monotonic() < deadline:
        N = min(max(N, d), max_N)
        remaining = deadline - time.monotonic()
        if remaining <= 0.5:
            break
        attempt_len = min(remaining, budget_per_attempt)
        cost, E = _anneal(N, d, D, rng, time.monotonic() + attempt_len)

        if cost == 0:
            consider(2 * N, [(a, b) for a, b in E])
            lo = max(lo, N)
            if hi is not None and N >= hi:
                hi = None
        else:
            hi = N if hi is None else min(hi, N)

        if lo >= max_N:
            break
        if hi is None:
            N = min(max_N, lo + max(1, lo // 12))
        elif hi - lo > 1:
            N = max(d, (lo + hi) // 2)
        else:
            N = hi

    if not lib.is_valid(best_n, best_e, d, D):
        n0, e0 = lib.haar_graph(d, range(d))
        return int(n0), [(int(u), int(v)) for u, v in e0]
    return best_n, best_e
