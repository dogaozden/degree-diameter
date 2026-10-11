import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cost: number of ordered (vertex, vertex) pairs at distance > D. Zero = valid.
# ----------------------------------------------------------------------------

def _cost(n, E, D):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb[v] = x
        ball = nb
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Annealing over degree-preserving 2-switches on a bipartite graph.
# Edges are stored as (a, b) with a on side A and b on side B.
# ----------------------------------------------------------------------------

def _anneal(n, E0, D, rng, deadline):
    E = list(E0)
    eset = set(E)
    cur = _cost(n, E, D)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        f = (now - t0) / span
        T = 0.1 + 1.5 * (1.0 - f)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in eset or n2 in eset:
            continue
        E[i] = n1
        E[j] = n2
        new = _cost(n, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add(n1)
            eset.add(n2)
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E if cur == 0 else None


# ----------------------------------------------------------------------------
# Growth: remove d edges with distinct endpoints, add a new A vertex x joined
# to their B ends and a new B vertex y joined to their A ends. Degrees are
# preserved and the graph stays bipartite.
# ----------------------------------------------------------------------------

def _grow(n, E, d, rng):
    pick = None
    for _ in range(200):
        order = list(range(len(E)))
        rng.shuffle(order)
        usedA, usedB, chosen = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            chosen.append(idx)
            if len(chosen) == d:
                break
        if len(chosen) == d:
            pick = chosen
            break
    if pick is None:
        return None
    pickset = set(pick)
    E2 = [e for i, e in enumerate(E) if i not in pickset]
    x, y = n, n + 1
    for idx in pick:
        a, b = E[idx]
        E2.append((x, b))
        E2.append((a, y))
    return E2


def _fallback(d):
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed * 1000003 + d * 131 + D)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return _fallback(d)[0], list(_fallback(d)[1])

    fb_n, fb_e = _fallback(d)
    best = [fb_n, list(fb_e)]
    best_n = fb_n

    def record(n, E):
        nonlocal best_n
        if n > best_n:
            edges = [tuple(e) for e in E]
            if lib.is_valid(n, edges, d, D):
                best[0], best[1] = n, edges
                best_n = n

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    moore = lib.moore_bound(d, D)

    # Phase 1: find a valid starting graph, shrinking N if annealing stalls.
    N = max(d + 1, int(0.45 * (moore // 2)))
    cur = None
    while cur is None:
        now = time.monotonic()
        if now >= deadline or N <= d:
            break
        S = rng.sample(range(N), d)
        E0 = [(i, N + (i + s) % N) for i in range(N) for s in S]
        slice_end = min(deadline, now + max(2.0, 0.3 * (deadline - now)))
        cur = _anneal(2 * N, E0, D, rng, slice_end)
        if cur is None:
            N = max(d, N - max(1, N // 20))

    # Phase 2: grow by two vertices at a time, re-annealing after each step.
    if cur is not None:
        n = 2 * N
        E = cur
        record(n, E)
        while time.monotonic() < deadline and n + 2 <= moore:
            now = time.monotonic()
            remaining = deadline - now
            slice_end = min(deadline, now + max(2.0, 0.3 * remaining))
            E2 = _grow(n, E, d, rng)
            if E2 is None:
                break
            res = _anneal(n + 2, E2, D, rng, slice_end)
            if res is not None:
                n += 2
                E = res
                record(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        fb_n, fb_e = _fallback(d)
        return fb_n, list(fb_e)
    return best[0], best[1]
