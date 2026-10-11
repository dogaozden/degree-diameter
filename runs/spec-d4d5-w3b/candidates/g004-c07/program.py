import math
import random
import time

import lib


def _cost(N, E, D):
    """Number of ordered vertex pairs not within distance D (0 means diameter <= D)."""
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        changed = False
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            if r != reach[v]:
                changed = True
            new.append(r)
        reach = new
        if not changed:
            break
    return sum(N - r.bit_count() for r in reach)


def _anneal(d, D, N, rng, deadline):
    """Simulated annealing over bipartite graphs on N = 2h vertices (sides 0..h-1 and h..N-1).

    Moves are degree-preserving double edge swaps, so every vertex keeps degree <= d.
    Returns the edge list if a diameter-<=D graph is found before the deadline, else None.
    """
    h = N // 2
    adjL = [set() for _ in range(h)]
    E = []
    for _ in range(d):
        perm = list(range(h))
        rng.shuffle(perm)
        for a in range(h):
            b = h + perm[a]
            if b not in adjL[a]:
                adjL[a].add(b)
                E.append((a, b))
    if len(E) < 2:
        return None

    cost = _cost(N, E, D)
    T0, T1 = 3.0, 0.15
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    T = T0
    it = 0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        if (it & 31) == 0:
            frac = min(1.0, (now - start) / span)
            T = T0 * (T1 / T0) ** frac
        it += 1

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adjL[a1] or b1 in adjL[a2]:
            continue

        E[i] = (a1, b2)
        E[j] = (a2, b1)
        adjL[a1].remove(b1)
        adjL[a1].add(b2)
        adjL[a2].remove(b2)
        adjL[a2].add(b1)

        c2 = _cost(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            adjL[a1].remove(b2)
            adjL[a1].add(b1)
            adjL[a2].remove(b1)
            adjL[a2].add(b2)

    if cost == 0:
        return list(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(time_limit * 0.85, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(fb_n, fb_e, d, D):
        fb_n, fb_e = 1, []
    best = (fb_n, fb_e)
    best_n = fb_n

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane meets the Moore bound when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Main search: annealed bipartite graphs, aiming one step above the current best order.
    N = best_n + 2
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = now + max(2.0, 0.4 * remaining)
        slice_end = min(slice_end, deadline)
        E = _anneal(d, D, N, rng, slice_end)
        if E is not None:
            consider(N, E)
            N = best_n + 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, fb_e)
    return best
