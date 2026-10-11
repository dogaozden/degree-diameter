import math
import random
import time

import lib


def _cost(n, adj, D):
    """Number of ordered vertex pairs at distance > D (0 means the diameter is at most D)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - b.bit_count() for b in ball)


def _circulant_start(N, d, rng):
    """d-regular bipartite graph on N + N vertices: A_a ~ B_{a+s} for distinct shifts s."""
    shifts = rng.sample(range(N), d)
    adj = [[] for _ in range(2 * N)]
    for a in range(N):
        for s in shifts:
            b = N + (a + s) % N
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _apply_switch(adj, a, i, c, j, x, y):
    """Replace edges a-x, c-y by a-y, c-x. Requires a-x, c-y present and a-y, c-x absent."""
    adj[a][i] = y
    adj[c][j] = x
    adj[x][adj[x].index(a)] = c
    adj[y][adj[y].index(c)] = a


def _anneal(N, d, D, rng, until):
    """Simulated annealing over d-regular bipartite graphs with N vertices per side.

    Moves are degree-preserving edge switches. Returns the adjacency lists when
    the diameter is at most D, or None if the time limit is reached first.
    """
    n = 2 * N
    adj = _circulant_start(N, d, rng)
    cur = _cost(n, adj, D)
    t_start = time.monotonic()
    span = max(1e-6, until - t_start)
    T0 = max(2.0, 0.02 * cur)
    while cur > 0:
        now = time.monotonic()
        if now >= until:
            return None
        frac = (now - t_start) / span
        T = max(0.3, T0 * (1.0 - frac))
        a = rng.randrange(N)
        c = rng.randrange(N)
        if a == c:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        x = adj[a][i]
        y = adj[c][j]
        if y in adj[a] or x in adj[c]:
            continue
        _apply_switch(adj, a, i, c, j, x, y)
        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _apply_switch(adj, a, i, c, j, y, x)  # reverts to a-x, c-y
    return adj


def _start_size(d, D, N_hi):
    """Initial number of vertices per side to try."""
    if (d, D) == (5, 5):
        return 169  # aim just above the record of 336 total vertices
    return max(d, int(0.5 * N_hi))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # D = 3 with d - 1 a prime power: the projective plane incidence graph is optimal.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    moore = lib._moore_bound(d, D)
    N_hi = moore // 2
    if N_hi < d:
        return best

    rng = random.Random(seed)
    lo = 0               # largest per-side size found valid
    hi = N_hi + 1        # smallest per-side size that failed
    N = _start_size(d, D, N_hi)

    while time.monotonic() < deadline:
        if N is None or N < d or N > N_hi or N <= lo or N >= hi:
            break
        now = time.monotonic()
        rem = deadline - now
        adj = _anneal(N, d, D, rng, now + 0.5 * rem)
        if adj is not None:
            lo = N
            edges = [(a, b) for a in range(N) for b in adj[a]]
            if 2 * N > best[0] and lib.is_valid(2 * N, edges, d, D):
                best = (2 * N, edges)
        else:
            hi = N

        # Choose the next size: step up while successful, bisect once a failure is known.
        if lo > 0 and hi > N_hi:
            N = lo + 1
        elif lo > 0:
            if hi - lo <= 1:
                break
            N = (lo + hi) // 2
        else:
            N = max(d, int(hi * 0.85))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
