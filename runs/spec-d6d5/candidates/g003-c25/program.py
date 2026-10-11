import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Abelian bi-Cayley (lifted) graphs over Z_m with k base vertices per side.
#
# Vertices: A_{i,g} = i*m + g and B_{j,h} = (k+j)*m + h, with g, h in Z_m.
# A dart (i, j, s) joins A_{i,g} to B_{j,g+s} for every g.
# Each layer is a permutation of the k base vertices, so every vertex gets
# degree d (before duplicate merging, which only lowers degree).
#
# Exact diameter check: translations act transitively on each of the two
# colour classes of base vertices, so it suffices to run BFS from one
# representative per base vertex (k on side A, k on side B) and check that
# every vertex is reached within distance D.
# ----------------------------------------------------------------------------


def _cost(k, m, D, darts, limit):
    """Number of (representative, vertex) pairs not reached within distance D.

    Zero means the lifted graph has diameter <= D. Returns early once the
    running total exceeds `limit`.
    """
    N = 2 * k * m
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ba = i * m
        bb = (k + j) * m
        for g in range(m):
            a = ba + g
            b = bb + (g + s) % m
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, m, darts):
    """Edge list of the lifted graph, deduplicated."""
    E = set()
    for i, j, s in darts:
        for g in range(m):
            E.add((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, sorted(E)


def _search(d, D, k, m, rng, deadline, iters):
    """Annealed search over voltages and per-layer target assignments.

    Returns (darts, cost). cost == 0 means a valid lift was found.
    Metropolis acceptance is pre-drawn: accept iff c2 <= cost - T*ln(u).
    """
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    cost = _cost(k, m, D, darts, float("inf"))
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, m, D, darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia = L * k + a
            ib = L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, m, D, darts, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # For D = 2, K_{d,d} is optimal for bipartite graphs.
    if D == 2:
        return best

    # D = 3 with d - 1 a prime power: projective plane incidence (Moore-optimal).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        consider(n0, e0)

    # Main search: abelian bi-Cayley lifts with k base vertices per side.
    ks = [1, 2, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        m = max(2, lo + rng.randrange(0, 8))
        darts, c = _search(d, D, k, m, rng, deadline, 700)
        if c == 0:
            n, e = _edges(k, m, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
