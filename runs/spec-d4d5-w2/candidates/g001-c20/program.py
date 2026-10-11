import math
import random
import time

import lib


def _circulant(N, d):
    """Simple d-regular bipartite graph on sides A=0..N-1 and B=0..N-1: a joins b=(a+k) mod N for k<d."""
    nbS = [set() for _ in range(2 * N)]
    edges = []
    for a in range(N):
        for k in range(d):
            b = (a + k) % N
            edges.append((a, b))
            nbS[a].add(N + b)
            nbS[N + b].add(a)
    return edges, nbS


def _valid_swap(i, j, edges, nbS, N):
    """Double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keeps degrees and simplicity."""
    if i == j:
        return False
    a1, b1 = edges[i]
    a2, b2 = edges[j]
    if a1 == a2 or b1 == b2:
        return False
    if (N + b2) in nbS[a1] or (N + b1) in nbS[a2]:
        return False
    return True


def _swap(i, j, edges, nbS, N):
    """Apply the double-edge swap in place. Calling it again on the same indices reverts it."""
    a1, b1 = edges[i]
    a2, b2 = edges[j]
    nbS[a1].discard(N + b1)
    nbS[N + b1].discard(a1)
    nbS[a2].discard(N + b2)
    nbS[N + b2].discard(a2)
    nbS[a1].add(N + b2)
    nbS[N + b2].add(a1)
    nbS[a2].add(N + b1)
    nbS[N + b1].add(a2)
    edges[i] = (a1, b2)
    edges[j] = (a2, b1)


def _bad(N, D, nbS):
    """Number of ordered vertex pairs at distance > D (bitmask BFS, bipartite sides 0..N-1 and N..2N-1)."""
    V = 2 * N
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = []
        for v in range(V):
            r = reach[v]
            for u in nbS[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(V - r.bit_count() for r in reach)


def _anneal(N, d, D, rng, t_end):
    """Search for a d-regular bipartite graph on 2N vertices with diameter <= D by simulated annealing.

    Returns the list of (a, b) pairs (b in 0..N-1 on the other side) or None if time ran out.
    """
    edges, nbS = _circulant(N, d)
    E = len(edges)
    for _ in range(4 * E):
        i = rng.randrange(E)
        j = rng.randrange(E)
        if _valid_swap(i, j, edges, nbS, N):
            _swap(i, j, edges, nbS, N)
    cur = _bad(N, D, nbS)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            return None
        frac = (now - t0) / span
        T = 1.5 * (1.0 - frac) + 0.05
        for _ in range(64):
            i = rng.randrange(E)
            j = rng.randrange(E)
            if not _valid_swap(i, j, edges, nbS, N):
                continue
            _swap(i, j, edges, nbS, N)
            new = _bad(N, D, nbS)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                if cur == 0:
                    break
            else:
                _swap(i, j, edges, nbS, N)
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    # Special case with a known optimal construction.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # Safe fallbacks.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    best_N = d
    best_edges = [(a, d + b) for a in range(d) for b in range(d)]  # K_{d,d}
    if not lib.is_valid(2 * d, best_edges, d, D):
        return 2, [(0, 1)]
    if D <= 2:
        return 2 * best_N, best_edges

    # Anneal-based search over increasing side sizes N (order n = 2N).
    moore = lib.moore_bound(d, D)
    N_max = moore // 2
    rng = random.Random(seed)
    inc = 8
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        if best_N + inc > N_max:
            inc = N_max - best_N
            if inc < 1:
                break
        N_try = best_N + inc
        slice_end = min(deadline, now + max(1.5, 0.35 * remaining))
        found = _anneal(N_try, d, D, rng, slice_end)
        if found is not None:
            cand = [(a, N_try + b) for a, b in found]
            if lib.is_valid(2 * N_try, cand, d, D):
                best_N = N_try
                best_edges = cand
                inc = min(inc * 2, 32)
                continue
        inc = max(1, inc // 2)

    n = 2 * best_N
    if not lib.is_valid(n, best_edges, d, D):
        return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]
    return n, best_edges
