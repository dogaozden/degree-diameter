"""Bold variant: random-start 2-switch annealing over bi-regular bipartite graphs.

Each attempt starts from a Haar-type circulant bipartite graph on N + N vertices
(valid, d-regular, bipartite, duplicate-free) and anneals with degree-preserving
2-switches to drive the count of vertex pairs at distance > D to zero. N is
grown by an adaptive step. Every returned graph is checked with lib.is_valid,
and the fallback K_{d,d} (or C_{2D} for d = 2) is kept throughout.
"""
import math
import random
import time

import lib


def _adj(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _bad(n, adj, D):
    """Number of ordered vertex pairs at distance more than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(N, d, D, deadline, rng, T0=2.0):
    """Anneal a d-regular bipartite graph on N + N vertices. Returns edge list or None."""
    n = 2 * N
    shifts = rng.sample(range(N), d)
    E = [(x, N + (x + s) % N) for s in shifts for x in range(N)]
    eset = set(E)
    cur = _bad(n, _adj(n, E), D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = max(0.05, T0 * (1.0 - (now - start) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        f1 = (a, e)
        f2 = (c, b)
        if f1 in eset or f2 in eset:
            continue
        E[i] = f1
        E[j] = f2
        new = _bad(n, _adj(n, E), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add(f1)
            eset.add(f2)
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return E


def _attempt(N, d, D, deadline, rng):
    E = _anneal(N, d, D, deadline, rng)
    if E is None:
        return None
    n = 2 * N
    edges = sorted(E)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if d <= 2:
        if d == 2 and D >= 3:
            n = 2 * D
            cand = (n, [(i, (i + 1) % n) for i in range(n)])
            if lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        return best

    if D == 2:
        return best

    # D = 3 algebraic candidates (cheap and usually strong).
    if D == 3:
        q = d - 1
        if lib.is_prime_power(q):
            cand = lib.projective_plane_incidence(q)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cand = lib.araujo_lopez_graph(d - 2)
                if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                    best = cand
            except Exception:
                pass

    # Adaptive growth of the side size N with annealing attempts.
    good = max(d, best[0] // 2)
    step = max(1, good // 4)
    while time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        budget = min(remaining, max(2.0, remaining / 3.0))
        N_try = good + step
        res = _attempt(N_try, d, D, time.monotonic() + budget, rng)
        if res is not None and res[0] > best[0]:
            best = res
            good = N_try
            step = min(step * 2, max(1, good // 8))
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
