import math
import random
import time

import lib


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (0 means valid)."""
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


def _kdd(d):
    """K_{d,d}: diameter 2, degree d, order 2d."""
    edges = [(i, d + j) for i in range(d) for j in range(d)]
    return 2 * d, edges


def _anneal(h, d, D, rng, cap):
    """Anneal a d-regular bipartite graph with h vertices per side.

    Starts from a Haar (circulant) graph and applies degree-preserving double edge
    swaps, minimising the number of pairs at distance > D. Returns an edge list
    or None if no zero-cost graph is found within cap seconds.
    """
    n = 2 * h
    shifts = rng.sample(range(h), d)
    adj = [[] for _ in range(n)]
    E = []
    Eset = set()
    for i in range(h):
        for s in shifts:
            a, b = i, h + (i + s) % h
            E.append([a, b])
            Eset.add((a, b))
            adj[a].append(b)
            adj[b].append(a)

    cur = _cost(n, adj, D)
    start = time.monotonic()
    m = len(E)
    while cur > 0:
        frac = (time.monotonic() - start) / cap
        if frac >= 1.0:
            break
        T = 2.0 * (1.0 - frac) + 0.05

        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue

        # Apply swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add((a1, b2))
        Eset.add((a2, b1))
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)

        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            # Revert.
            Eset.discard((a1, b2))
            Eset.discard((a2, b1))
            Eset.add((a1, b1))
            Eset.add((a2, b2))
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)

    if cur == 0:
        return [(a, b) for a, b in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = _kdd(d)
    if D == 2:
        return best_n, best_e

    # Structured D = 3 case: projective plane incidence graph.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    moore = lib._moore_bound(d, D)
    mh = moore // 2  # a bipartite graph with h vertices per side has order 2h <= moore

    # Ladder/bisection over the side size h, using the annealer as the feasibility test.
    lo = d
    hi = None
    cur = max(lo + 1, int(0.45 * mh))
    while time.monotonic() < deadline - 0.5:
        if cur > mh:
            cur = mh
        if cur <= lo:
            break
        remaining = deadline - time.monotonic()
        cap = max(1.0, remaining * 0.35)
        res = _anneal(cur, d, D, rng, cap)
        if res is not None and lib.is_valid(2 * cur, res, d, D):
            lo = cur
            best_n, best_e = 2 * cur, res
        else:
            hi = cur

        if hi is None:
            if lo >= mh:
                break
            cur = lo + max(1, (mh - lo) // 6)
        else:
            if hi - lo <= 1:
                break
            cur = (lo + hi) // 2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = _kdd(d)
    return best_n, best_e
