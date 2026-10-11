import math
import random
import time

import lib


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (adj: list of sets)."""
    full = (1 << n) - 1
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if all(r == full for r in reach):
            return 0
    return sum(n - r.bit_count() for r in reach) // 2


def _apply_swap(adj, E, i1, i2):
    """Replace edges (u1,v1),(u2,v2) by (u1,v2),(u2,v1) in place."""
    u1, v1 = E[i1]
    u2, v2 = E[i2]
    adj[u1].discard(v1); adj[v1].discard(u1)
    adj[u2].discard(v2); adj[v2].discard(u2)
    adj[u1].add(v2); adj[v2].add(u1)
    adj[u2].add(v1); adj[v1].add(u2)
    E[i1] = (u1, v2)
    E[i2] = (u2, v1)


def _undo_swap(adj, E, i1, i2):
    """Reverse _apply_swap."""
    u1, v2 = E[i1]
    u2, v1 = E[i2]
    adj[u1].discard(v2); adj[v2].discard(u1)
    adj[u2].discard(v1); adj[v1].discard(u2)
    adj[u1].add(v1); adj[v1].add(u1)
    adj[u2].add(v2); adj[v2].add(u2)
    E[i1] = (u1, v1)
    E[i2] = (u2, v2)


def _anneal_regular(N, d, D, rng, deadline, iters):
    """Search a d-regular bipartite graph with N+N vertices and diameter <= D.

    Starts from a Haar graph on Z_N (a random d-subset of shifts) and applies
    degree-preserving 2-switches, annealing on the number of bad pairs.
    Returns (n, edges) on success, else None.
    """
    n = 2 * N
    shifts = rng.sample(range(N), d)
    adj = [set() for _ in range(n)]
    E = []
    for i in range(N):
        for s in shifts:
            u, v = i, N + (i + s) % N
            E.append((u, v))
            adj[u].add(v)
            adj[v].add(u)

    cost = _bad_pairs(n, adj, D)
    T0, T_end = 1.0, 0.1
    m = len(E)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i1 = rng.randrange(m)
        i2 = rng.randrange(m)
        if i1 == i2:
            continue
        u1, v1 = E[i1]
        u2, v2 = E[i2]
        if u1 == u2 or v1 == v2:
            continue
        if v2 in adj[u1] or v1 in adj[u2]:
            continue
        _apply_swap(adj, E, i1, i2)
        T = T0 * (T_end / T0) ** (it / max(1, iters))
        new_cost = _bad_pairs(n, adj, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
        else:
            _undo_swap(adj, E, i1, i2)

    if cost == 0:
        return n, list(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if d == 2 and D >= 2:
        # Even cycle C_{2D} is bipartite with diameter D.
        cyc = [(i, (i + 1) % (2 * D)) for i in range(2 * D)]
        cyc = [(min(u, v), max(u, v)) for u, v in cyc]
        if lib.is_valid(2 * D, cyc, d, D):
            best = (2 * D, cyc)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective plane incidence graph (diameter 3) when d-1 is a prime power.
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n_pg, e_pg = lib.projective_plane_incidence(d - 1)
        consider(n_pg, e_pg)

    # New family: near-regular bipartite graphs found by annealed 2-switch search.
    if D >= 3 and d >= 3:
        N = max(d, best[0] // 2 + 1)
        fails = 0
        while time.monotonic() < deadline and fails < 3:
            res = _anneal_regular(N, d, D, rng, deadline, iters=6000)
            if res is not None:
                consider(res[0], res[1])
                N = max(N + 1, best[0] // 2 + 1)
                fails = 0
            else:
                fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
