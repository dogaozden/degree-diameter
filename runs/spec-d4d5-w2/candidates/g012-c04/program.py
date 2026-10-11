import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fast diameter-defect counter on bitmasks.
# ----------------------------------------------------------------------------

def _count_bad(n, adj, D):
    """Ordered vertex pairs at distance > D (disconnected pairs count). Zero iff diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# Family 1: Haar graphs (bi-Cayley over Z_m) found by hill-climbing the
# connection set S. Distances from a_0 and b_0 determine the whole diameter,
# so the cost is cheap even for large m.
# ----------------------------------------------------------------------------

def _haar_adj(m, S):
    adj = [[] for _ in range(2 * m)]
    for i in range(m):
        for s in S:
            j = (i + s) % m
            adj[i].append(m + j)
            adj[m + j].append(i)
    return adj


def _haar_search(d, D, m, rng, deadline, iters):
    """Find S (|S| = d, distinct, containing 0) in Z_m with Haar graph diameter <= D, or None."""
    if m < d or d < 2:
        return None
    others = list(range(1, m))

    def cost(S):
        return _count_bad(2 * m, _haar_adj(m, S), D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        cand = rng.choice(others)
        if cand in S:
            continue
        T = S[:]
        T[i] = cand
        ct = cost(T)
        if ct <= c or rng.random() < 0.02:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Family 2: 2-switch annealing on d-regular bipartite graphs with N + N vertices.
# Starts from a random Haar graph of the target size and minimizes the number
# of ordered pairs at distance > D. Degrees and bipartiteness are preserved
# by construction, and the search is not restricted to any symmetry group.
# ----------------------------------------------------------------------------

def _random_start(N, d, rng):
    S = rng.sample(range(N), d)
    return [(i, N + (i + s) % N) for i in range(N) for s in S]


def _anneal_bip(N, d, D, E, rng, deadline, T0, T1):
    n = 2 * N
    E = list(E)
    eset = set(E)

    def adjacency():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(b)
            adj[b].append(a)
        return adj

    cost = _count_bad(n, adjacency(), D)
    if cost == 0:
        return E
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        new_cost = _count_bad(n, adjacency(), D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return E if cost == 0 else None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(res):
        nonlocal best, best_n
        n, e = res
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence graph (exact record for d = 3, D = 3 when d-1 is a prime power).
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            consider(lib.projective_plane_incidence(q))
            break

    # Haar graph search, scanning group orders just above the current best.
    haar_deadline = start + 0.45 * (deadline - start)
    m = max(d + 1, best_n // 2 + 1)
    misses = 0
    while time.monotonic() < haar_deadline and misses < 4:
        S = _haar_search(d, D, m, rng, haar_deadline, 300)
        if S is not None:
            consider(lib.haar_graph(m, S))
            misses = 0
        else:
            misses += 1
        m += 1

    # Bipartite 2-switch annealing at sizes just above the current best.
    total = deadline - start
    chunk = max(3.0, 0.25 * total)
    while time.monotonic() < deadline:
        N = max(best_n // 2 + 1, d + 1)
        E = _random_start(N, d, rng)
        budget_end = min(deadline, time.monotonic() + chunk)
        E2 = _anneal_bip(N, d, D, E, rng, budget_end, 3.0, 0.3)
        if E2 is not None:
            consider((2 * N, [(a, b) for a, b in E2]))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
