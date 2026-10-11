import math
import random
import time

import lib


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _largest_pp_below(d):
    """Largest prime power q with q + 1 <= d (so PG(2, q) has degree q + 1 <= d), or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _cost(n, E, D):
    """Ordered pairs (x, y) with dist > D in the bipartite graph on n+n vertices given by edge list E."""
    N = 2 * n
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(n + b)
        adj[n + b].append(a)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(N - b.bit_count() for b in ball)


def _random_regular(n, d, rng):
    """Random simple d-regular bipartite graph as (E, S): union of d random perfect matchings."""
    E, S = [], set()
    for _ in range(d):
        for _try in range(200):
            p = list(range(n))
            rng.shuffle(p)
            if all((i, p[i]) not in S for i in range(n)):
                break
        else:
            return None
        for i in range(n):
            E.append((i, p[i]))
            S.add((i, p[i]))
    return E, S


def _grow_one(n, E, S, d, rng):
    """Add one left vertex n and one right vertex n, keeping all degrees at d.

    Picks d edges (x, y) with distinct x and distinct y, replaces each by (n, y),
    and appends (x, n). Returns False if no such d edges exist.
    """
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedx, usedy, picks = set(), set(), []
    for t in idx:
        x, y = E[t]
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        picks.append(t)
        if len(picks) == d:
            break
    if len(picks) < d:
        return False
    for t in picks:
        x, y = E[t]
        S.discard((x, y))
        E[t] = (n, y)
        S.add((n, y))
        E.append((x, n))
        S.add((x, n))
    return True


def _search(d, D, n, rng, deadline, best, bound):
    """Simulated annealing over d-regular bipartite graphs with n+n vertices, growing n on success."""
    init = None
    while init is None and time.monotonic() < deadline:
        init = _random_regular(n, d, rng)
    if init is None:
        return best
    E, S = init
    cost = _cost(n, E, D)
    chunk_len = 4.0
    chunk_start = time.monotonic()

    while time.monotonic() < deadline:
        if cost == 0:
            if 2 * n > best[0]:
                edges = [(a, n + b) for a, b in E]
                if lib.is_valid(2 * n, edges, d, D):
                    best = (2 * n, edges)
            if 2 * (n + 1) > bound or not _grow_one(n, E, S, d, rng):
                break
            n += 1
            cost = _cost(n, E, D)
            chunk_start = time.monotonic()
            continue

        now = time.monotonic()
        if now - chunk_start >= chunk_len:
            chunk_start = now
        f = (now - chunk_start) / chunk_len
        T = 1.2 * (1.0 - f) + 0.08

        i, j = rng.sample(range(len(E)), 2)
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in S or (c, b) in S:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        c2 = _cost(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S.discard((a, b))
            S.discard((c, e))
            S.add((a, e))
            S.add((c, b))
            cost = c2
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # cycle C_{2D} is bipartite with diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D == 2:
        return best

    # D == 3 structured constructions.
    if D >= 3:
        q = _largest_pp_below(d)
        if q is not None:
            n_pg, e_pg = lib.projective_plane_incidence(q)
            if n_pg > best[0] and lib.is_valid(n_pg, e_pg, d, D):
                best = (n_pg, e_pg)
            if D == 3 and q == d - 1:
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_al, e_al = lib.araujo_lopez_graph(d - 2)
                if n_al > best[0] and lib.is_valid(n_al, e_al, d, D):
                    best = (n_al, e_al)
            except (ValueError, StopIteration):
                pass
        if D == 3:
            return best

    # D >= 4: annealed search for bipartite d-regular graphs, growing one vertex pair at a time.
    bound = _moore(d, D)
    n0 = max(d, best[0] // 2 + 1)
    best = _search(d, D, n0, rng, deadline, best, bound)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
