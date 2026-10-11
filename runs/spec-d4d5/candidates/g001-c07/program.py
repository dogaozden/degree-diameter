"""Bi-Cayley (Haar-type) graphs over semidirect products Z_m x| Z_k, found by annealing.

Construction: for a group G of order N, pick a connection set S of size d containing
the identity. The bipartite graph has parts A = G and B = G, with a_x adjacent to b_{x*g}
for g in S. Each vertex has degree d, the graph is simple and bipartite, and left
multiplication by any h is an automorphism. Diameter <= D therefore reduces to two BFS
runs, one from a_e and one from b_e, so a connection set can be scored cheaply. The
search anneals over S, minimising the number of vertices not reached within D steps.
Non-abelian groups are tried as well as cyclic ones.
"""
import math
import random
import time

import lib


def _group_specs(N, rng, max_r=6):
    """Semidirect factorisations N = m*k as (m, k, r) triples, shuffled."""
    specs = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k == 1:
            specs.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:max_r]:
            specs.append((m, k, r))
    rng.shuffle(specs)
    return specs


def _table(spec):
    """Multiplication table MT[x][y] and inverse list IV for the group described by spec."""
    m, k, r = spec
    N = m * k
    _, mul, inv = lib.semidirect_group(m, k, r)
    MT = [[mul(x, y) for y in range(N)] for x in range(N)]
    IV = [inv(x) for x in range(N)]
    return MT, IV


def _unreached(N, MT, S, invS, D, src):
    """Number of the 2N vertices not reached from src within D steps."""
    seen = bytearray(2 * N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for node in frontier:
            if node < N:
                row = MT[node]
                for g in S:
                    t = N + row[g]
                    if not seen[t]:
                        seen[t] = 1
                        nxt.append(t)
            else:
                row = MT[node - N]
                for gi in invS:
                    t = row[gi]
                    if not seen[t]:
                        seen[t] = 1
                        nxt.append(t)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return 2 * N - cnt


def _cost(N, MT, IV, S, D):
    """Bad count for connection set S. Zero iff the bi-Cayley graph has diameter <= D."""
    invS = [IV[g] for g in S]
    return _unreached(N, MT, S, invS, D, 0) + _unreached(N, MT, S, invS, D, N)


def _anneal(N, MT, IV, d, D, rng, t_end, max_iters=3000):
    """Anneal a connection set of size d (containing 0 = identity). Return it, or None."""
    if N <= d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, MT, IV, S, D)
    T = 1.5
    for _ in range(max_iters):
        if cur == 0:
            return S
        if time.monotonic() >= t_end:
            return None
        i = rng.randrange(1, d)
        while True:
            c = rng.randrange(1, N)
            if c not in S:
                break
        S2 = S[:]
        S2[i] = c
        new = _cost(N, MT, IV, S2, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            S, cur = S2, new
        T = max(0.25, T * 0.998)
    return S if cur == 0 else None


def _edges(N, MT, S):
    """Edge list of the bi-Cayley graph: A-vertex x is joined to B-vertex N + x*g for g in S."""
    edges = []
    for x in range(N):
        row = MT[x]
        for g in S:
            edges.append((x, N + row[g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 0.5

    # Calibration case: the projective plane meets the Moore bound.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Trivial cases.
    if d <= 1 or D <= 0:
        return (1, []) if D <= 0 or d <= 0 else (2, [(0, 1)])
    if D == 1:
        return 2, [(0, 1)]

    # Baseline: K_{d,d} has diameter 2 and degree d.
    best = (2, [(0, 1)])
    if D >= 2:
        n0, e0 = lib.haar_graph(d, range(d))
        if lib.is_valid(n0, e0, d, D):
            best = (n0, e0)

    rng = random.Random(seed)
    N = d + 1
    while N <= 600 and time.monotonic() < deadline - 0.2:
        now = time.monotonic()
        remaining = deadline - now
        budget = min(max(1.0, 0.15 * remaining), 12.0)
        n_end = min(deadline, now + budget)

        specs = _group_specs(N, rng)
        tables = {}
        found = None
        idx = 0
        while found is None and specs and time.monotonic() < n_end:
            spec = specs[idx % len(specs)]
            idx += 1
            if spec not in tables:
                tables[spec] = _table(spec)
            MT, IV = tables[spec]
            t_end = min(n_end, time.monotonic() + 0.3)
            S = _anneal(N, MT, IV, d, D, rng, t_end)
            if S is not None:
                found = (MT, S)

        if found is not None:
            MT, S = found
            n = 2 * N
            edges = _edges(N, MT, S)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        N += 1

    return best
