import math
import random
import time

import numpy as np

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


# ---------------------------------------------------------------- group-Haar search (D = 3)
#
# Group Haar graph H(G, S): vertices a_x, b_y (x, y in G); a_x ~ b_{x*g} for g in S.
# It is bipartite and d-regular when |S| = d. Left multiplication by h maps
# a_x -> a_{hx}, b_y -> b_{hy}, an automorphism, and it is transitive on each side.
# So diameter <= 3 holds iff BFS from a_e and from b_e reaches everything within 3 steps.
# WLOG e in S (relabel the B side). We run simulated annealing over S with cost equal to
# the number of vertices missed by those two BFS runs. Non-abelian groups (semidirect
# products Z_m x| Z_k) are included, unlike the cyclic-only parent search.

def _group_specs(N):
    """Return group descriptions of order N: the cyclic group plus semidirect products Z_m x| Z_k."""
    specs = [("cyc", N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            specs.append(("sd", m, k, r))
    return specs


def _group_tables(spec):
    """Return (order, multiplication table, inverse list) for a group spec."""
    if spec[0] == "cyc":
        N = spec[1]

        def mul(x, y):
            return (x + y) % N

        def inv(x):
            return (-x) % N
    else:
        N, mul, inv = lib.semidirect_group(spec[1], spec[2], spec[3])
    table = [[mul(x, y) for y in range(N)] for x in range(N)]
    invs = [inv(x) for x in range(N)]
    return N, table, invs


def _unreached(adj, src, n):
    """Number of vertices at distance > 3 from src."""
    seen = [False] * n
    seen[src] = True
    front = [src]
    cnt = 1
    for _ in range(3):
        nxt = []
        for v in front:
            for u in adj[v]:
                if not seen[u]:
                    seen[u] = True
                    nxt.append(u)
        cnt += len(nxt)
        front = nxt
    return n - cnt


def _cost(S, N, table, invs):
    """Missed-vertex count from a_e and b_e for the Haar graph with connection set S."""
    n = 2 * N
    adj = [None] * n
    for x in range(N):
        adj[x] = [N + table[x][g] for g in S]
    Sinv = [invs[g] for g in S]
    for y in range(N):
        adj[N + y] = [table[y][h] for h in Sinv]
    return _unreached(adj, 0, n) + _unreached(adj, N, n)


def _search(d, N, table, invs, rng, deadline):
    """Anneal a d-subset S of G containing the identity (0) with zero cost, or return None."""
    if d < 2 or d - 1 > N - 1:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cost = _cost(S, N, table, invs)
    T = 0.5
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, d)
        new = rng.randrange(1, N)
        if new in S:
            continue
        S2 = list(S)
        S2[i] = new
        c2 = _cost(S2, N, table, invs)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            S, cost = S2, c2
    return S


def _group_search(d, best, rng, deadline):
    """Escalate the group order N upward from the current best, trying each group of order N."""
    N_hi = d * d - d + 1  # a-side coverage S S^{-1} needs |G| <= d^2 - d + 1
    N = max(d, best[0] // 2 + 1)
    while N <= N_hi and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        per_N = max(0.2, 0.3 * remaining)
        n_end = min(deadline, now + per_N)
        specs = _group_specs(N)
        rng.shuffle(specs)
        for spec in specs:
            t = time.monotonic()
            if t >= n_end:
                break
            sub = min(n_end, t + max(0.05, per_N / max(1, len(specs))))
            try:
                N_, table, invs = _group_tables(spec)
            except ValueError:
                continue
            S = _search(d, N_, table, invs, rng, sub)
            if S is not None:
                n = 2 * N_
                edges = [(x, N_ + table[x][g]) for x in range(N_) for g in S]
                if n > best[0] and lib.is_valid(n, edges, d, 3):
                    best = (n, edges)
                break
        N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    if D == 3:
        try:
            best = _group_search(d, best, rng, deadline)
        except Exception:
            best = kdd
    else:
        # Random Haar fallback for other diameters.
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= deadline:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, edges = lib.haar_graph(m, S)
                if lib.within_diameter(n, edges, D):
                    found = (n, edges)
                    break
            if found:
                if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                    best = found
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return kdd
    return best
