import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction for D >= 3: bipartite d-regular graphs found by annealing
# over degree-preserving edge switches. Each candidate has N vertices per side,
# so the order is 2N. The cost is the number of ordered vertex pairs at distance
# more than D. A circulant start gives a simple d-regular bipartite graph, then
# switches move it toward diameter D. Cost 0 means a valid graph.
#
# Fallbacks: K_{d,d} (valid for D >= 2), plus the projective-plane and
# Araujo-Pardo-Lopez graphs for D = 3.
# ----------------------------------------------------------------------------


def _graph_adj(N, ea, eb):
    """Adjacency lists of the bipartite graph: A-vertex a is node a, B-vertex b is node N + b."""
    adj = [[] for _ in range(2 * N)]
    for a, b in zip(ea, eb):
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _cost(N, D, ea, eb):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
    n = 2 * N
    adj = _graph_adj(N, ea, eb)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball)


def _attempt(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with N+N vertices to diameter <= D.

    Returns the edge list [(a, b)] on success, or None if the deadline passes first.
    """
    shifts = rng.sample(range(N), d)
    ea = [a for a in range(N) for _ in shifts]
    eb = [(a + s) % N for a in range(N) for s in shifts]
    eset = set(a * N + b for a, b in zip(ea, eb))
    M = len(ea)
    c = _cost(N, D, ea, eb)
    T = 1.0
    while c > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        a1, b1 = ea[i], eb[i]
        a2, b2 = ea[j], eb[j]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * N + b2
        k2 = a2 * N + b1
        if k1 in eset or k2 in eset:
            continue
        # Switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are preserved.
        eb[i] = b2
        eb[j] = b1
        eset.discard(a1 * N + b1)
        eset.discard(a2 * N + b2)
        eset.add(k1)
        eset.add(k2)
        c2 = _cost(N, D, ea, eb)
        T = max(0.05, T * 0.999)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2
        else:
            # Undo the switch.
            eb[i] = b1
            eb[j] = b2
            eset.discard(k1)
            eset.discard(k2)
            eset.add(a1 * N + b1)
            eset.add(a2 * N + b2)
    return list(zip(ea, eb))


def _switch_search(d, D, best_n, deadline, rng, consider, moore):
    """Grow N (vertices per side) while annealing succeeds; each success is offered to consider()."""
    N = max(d, best_n // 2 + 1)
    step = max(2, N // 25)
    while time.monotonic() < deadline:
        if 2 * N > moore:
            break
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, (deadline - now) / 3))
        edges = _attempt(N, d, D, rng, slice_end)
        if edges is not None:
            e = [(a, N + b) for a, b in edges]
            consider(2 * N, e)
            N += step
        else:
            step = max(1, step // 2)


# ----------------------------------------------------------------------------
# Algebraic families for small D.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D == 2:
        return best_n, best_e

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    moore = lib.moore_bound(d, D)
    _switch_search(d, D, best_n, deadline, rng, consider, moore)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
