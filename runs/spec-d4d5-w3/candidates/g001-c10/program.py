"""Bi-Cayley search over small groups, with a two-root eccentricity test.

Construction: for a finite group G of order N and a connection set S of size d,
the bi-Cayley graph has vertices (g, 0) and (g, 1) for g in G, and edges
(g, 0) -- (g*s, 1) for s in S. Left multiplication by any x in G is an
automorphism that preserves both sides, so the diameter is at most D exactly
when the eccentricities of the two identity vertices (1,0) and (1,1) are at
most D. The search therefore only needs two BFS runs per candidate.

Connection sets are improved by simulated annealing that minimizes the number
of vertices unreached within D steps from those two roots. Groups are the
metacyclic semidirect products Z_m x| Z_k of each order N, scanned upward in N.
"""
import math
import random
import time

import lib


def _groups(N):
    """All semidirect products Z_m x| Z_k with m*k = N, as (m, k, r) triples."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def _unreached(adj, root, D, n):
    """Number of vertices not within distance D of root."""
    seen = bytearray(n)
    seen[root] = 1
    frontier = [root]
    cnt = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            for u in adj[v]:
                if not seen[u]:
                    seen[u] = 1
                    nxt.append(u)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return n - cnt


def _cost(N, M, S, D):
    """Count of unreached (vertex, root) pairs for the two identity roots; 0 iff diameter <= D."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for g in range(N):
        Mg = M[g]
        for s in S:
            h = N + Mg[s]
            adj[g].append(h)
            adj[h].append(g)
    return _unreached(adj, 0, D, n) + _unreached(adj, N, D, n)


def _anneal(N, M, d, D, rng, iters, deadline):
    """Anneal a connection set S of size d in G; return S with cost 0, or None."""
    S = rng.sample(range(N), d)
    cost = _cost(N, M, S, D)
    T = 2.0
    for it in range(iters):
        if cost == 0:
            return S
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(N, M, S2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
        T = max(0.2, T * 0.998)
    return S if cost == 0 else None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.3 * time_limit, min(0.8 * time_limit, time_limit - 4.0))

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Fallback that is always valid for D >= 2: K_{d,d}.
    best_n = 2 * d
    best_edges = [(i, d + j) for i in range(d) for j in range(d)]

    rng = random.Random(seed)
    N = d + 1
    while time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        result = None
        for (m, k, r) in groups[:8]:
            if time.monotonic() >= deadline:
                break
            _, mul, _ = lib.semidirect_group(m, k, r)
            M = [[mul(x, y) for y in range(N)] for x in range(N)]
            S = _anneal(N, M, d, D, rng, 1500, deadline)
            if S is not None:
                result = (M, S)
                break
        if result is not None:
            M, S = result
            edges = [(g, N + M[g][s]) for g in range(N) for s in S]
            if 2 * N > best_n and lib.is_valid(2 * N, edges, d, D):
                best_n, best_edges = 2 * N, edges
        N += 1

    return best_n, best_edges
