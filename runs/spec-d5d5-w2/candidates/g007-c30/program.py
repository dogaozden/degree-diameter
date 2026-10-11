import math
import random
import time

import lib


def _swap(adj, N, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1) in adjacency lists.
    A side is 0..N-1, B side is N..2N-1 (B index = N + b)."""
    B1, B2 = N + b1, N + b2
    adj[a1][adj[a1].index(B1)] = B2
    adj[B2][adj[B2].index(a2)] = a1
    adj[a2][adj[a2].index(B2)] = B1
    adj[B1][adj[B1].index(a1)] = a2


def _cost(n, adj, D):
    """Number of ordered vertex pairs not within distance D (0 means valid diameter)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on N+N vertices toward diameter <= D.

    Starts from a random Haar graph (valid, simple, d-regular) and applies
    degree-preserving edge switches. Temperature decays with elapsed time.
    Returns the edge list [(a, b)] with b in 0..N-1 if diameter <= D, else None.
    """
    n = 2 * N
    shifts = rng.sample(range(N), d)
    E = [(a, (a + s) % N) for a in range(N) for s in shifts]
    pairs = set(E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    cur = _cost(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 2.0 * (1.0 - frac) + 0.3
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in pairs or (a2, b1) in pairs:
            continue
        _swap(adj, N, a1, b1, a2, b2)
        c2 = _cost(n, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            pairs.discard((a1, b1))
            pairs.discard((a2, b2))
            pairs.add((a1, b2))
            pairs.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            cur = c2
        else:
            _swap(adj, N, a1, b2, a2, b1)
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3 with d - 1 a prime power: projective plane incidence meets the Moore bound.
    if D == 3:
        q = d - 1
        if lib.is_prime_power(q):
            consider(*lib.projective_plane_incidence(q))
            if lib.is_valid(best[0], best[1], d, D) and best[0] >= moore:
                return best

    # Main search: chase the frontier N (sides of size N, total 2N) with annealing.
    slice_len = max(3.0, 0.2 * budget)
    while time.monotonic() < deadline:
        N = max(d, best[0] // 2 + 1)
        if 2 * N > moore:
            break
        att_deadline = min(deadline, time.monotonic() + slice_len)
        E = _anneal(N, d, D, rng, att_deadline)
        if E is not None:
            consider(2 * N, [(a, N + b) for a, b in E])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
