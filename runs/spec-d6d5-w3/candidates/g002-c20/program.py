import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap algebraic bases (used as the starting size and as the safe fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Different construction: random-start d-regular bipartite graphs, optimised
# directly on the graph by degree-preserving double-edge swaps (simulated
# annealing on the number of vertex pairs at distance > D). No voltage group.
# ----------------------------------------------------------------------------

def _cost(N, adj, D):
    """Number of ordered (vertex, vertex) pairs at distance > D; zero means diameter <= D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _sa_regular(d, D, L, rng, deadline):
    """Search for a d-regular bipartite graph with L + L vertices and diameter <= D.

    Left vertices are 0..L-1, right vertices are L..2L-1. Returns (N, edges) or None.
    """
    N = 2 * L
    edges = []
    eset = set()
    adj = [[] for _ in range(N)]
    for i in range(L):
        for s in range(d):
            x, y = i, L + (i + s) % L
            edges.append([x, y])
            eset.add(x * N + y)
            adj[x].append(y)
            adj[y].append(x)
    m = len(edges)

    def do_swap(i, j, x, y, z, w):
        # Requires edges[i] == [x, y] and edges[j] == [z, w].
        # Replaces them by [x, w] and [z, y]; degrees are unchanged.
        eset.discard(x * N + y)
        eset.discard(z * N + w)
        eset.add(x * N + w)
        eset.add(z * N + y)
        adj[x].remove(y); adj[x].append(w)
        adj[y].remove(x); adj[y].append(z)
        adj[z].remove(w); adj[z].append(y)
        adj[w].remove(z); adj[w].append(x)
        edges[i] = [x, w]
        edges[j] = [z, y]

    def propose(rng):
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            return None
        x, y = edges[i]
        z, w = edges[j]
        if x == z or y == w:
            return None
        if x * N + w in eset or z * N + y in eset:
            return None
        return i, j, x, y, z, w

    # Randomise the circulant start with valid swaps (no cost evaluation needed).
    done = 0
    tries = 0
    while done < 4 * m and tries < 40 * m:
        tries += 1
        mv = propose(rng)
        if mv is None:
            continue
        do_swap(*mv)
        done += 1
    if time.monotonic() >= deadline:
        return None

    cur = _cost(N, adj, D)
    T = 3.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        T = max(0.2, T * 0.999)
        mv = propose(rng)
        if mv is None:
            continue
        i, j, x, y, z, w = mv
        do_swap(i, j, x, y, z, w)
        new = _cost(N, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            do_swap(i, j, x, w, z, y)  # undo
    return N, [(u, v) for u, v in edges]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration shortcut: a graph already at the Moore bound cannot be beaten.
    if best_n >= moore:
        return best

    if d >= 3 and D >= 3:
        # Bisect the number of vertices per side. Each attempt is a regular
        # bipartite annealing run; a success raises the feasible side, a failure
        # lowers the ceiling.
        lo = max(best_n // 2, d + 1)
        hi = moore // 2
        while lo < hi and time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            mid = (lo + hi + 1) // 2
            att = min(deadline, time.monotonic() + max(1.0, 0.35 * remaining))
            res = _sa_regular(d, D, mid, rng, att)
            if res is not None:
                consider(res[0], res[1])
                lo = mid
            else:
                hi = mid - 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
