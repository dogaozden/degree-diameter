import math
import random
import time

import lib

BIG = 10 ** 9


def _cost(k, m, D, darts):
    """Number of (representative, vertex) pairs not reached within D in the abelian bi-Cayley lift.

    Vertices: A_{i,x} = i*m + x and B_{j,y} = k*m + j*m + y, for Z_m. Dart (i, j, s) joins
    A_{i,x} to B_{j,x+s}. Translation by Z_m acts transitively on each side, so one source per
    base vertex suffices. Zero means the lift has diameter <= D.
    """
    seen = set()
    for i, j, s in darts:
        key = (i, j, s % m)
        if key in seen:
            return BIG
        seen.add(key)
    N = 2 * k * m
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        base_b = k * m + j * m
        for x in range(m):
            a = i * m + x
            b = base_b + (x + s) % m
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    srcs = [i * m for i in range(k)] + [k * m + j * m for j in range(k)]
    for src in srcs:
        vis = bytearray(N)
        vis[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not vis[v]:
                        vis[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
    return total


def _lift_edges(k, m, darts):
    """Edge list and order of the lift described by darts."""
    E = []
    for i, j, s in darts:
        for x in range(m):
            E.append((i * m + x, k * m + j * m + (x + s) % m))
    return 2 * k * m, E


def _search(k, m, d, D, rng, deadline, budget):
    """Anneal voltages and layer permutations for a d-regular abelian bi-Cayley lift.

    Layer L is a permutation p_L of range(k): dart (i, p_L[i], s) for each i. That gives
    every base vertex degree d on each side. Returns darts with zero cost, or None.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    c = _cost(k, m, D, darts)
    T = 1.0
    ev = 1
    while c > 0 and ev < budget and time.monotonic() < deadline:
        new = [r[:] for r in darts]
        if k == 1 or rng.random() < 0.6:
            new[rng.randrange(len(new))][2] = rng.randrange(m)
        else:
            L = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            a, b = L * k + i1, L * k + i2
            new[a][1], new[b][1] = new[b][1], new[a][1]
        c2 = _cost(k, m, D, new)
        ev += 1
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            darts, c = new, c2
        T = max(0.2, T * 0.997)
    return darts if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2 and is the Moore-optimal graph for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    # Projective plane incidence graph meets the Moore bound when d-1 is a prime power.
    if d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    if best_n >= moore:
        return best_n, best_e

    rng = random.Random(seed * 7919 + d * 131 + D)
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 2, 2, 3])
        lo = best_n // (2 * k) + 1
        m_max = moore // (2 * k)
        if lo > m_max:
            continue
        m = lo + rng.randrange(max(1, lo // 20))
        if m > m_max:
            m = lo
        if m < d and k == 1:
            m = d
            if m > m_max:
                continue
        darts = _search(k, m, d, D, rng, deadline, budget=1000)
        if darts is not None:
            n, e = _lift_edges(k, m, darts)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
