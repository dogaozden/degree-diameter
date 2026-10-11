import random
import time
from math import gcd

import lib


# Construction: bipartite Cayley graphs (generalized Haar graphs) over small finite
# groups. Vertices are A_x = x and B_x = N + x for x in G. Connection set S (|S| = d)
# gives edges A_x -- B_{x*s}. Left multiplication is an automorphism that is regular
# on each side, so the diameter check only needs BFS from A_e and B_e. Connection sets
# are found by hill-climbing on the number of vertices not reached within D steps.
# Groups are cyclic and Z_m x|_r Z_k, searched order by order upward from d+1.
# Fallback is K_{d,d}, which is always valid.


def _table(N, mul):
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _groups(N, rng):
    out = []
    _, mul, inv = lib.cyclic_group(N)
    out.append((mul, inv))
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        cands = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(cands)
        for r in cands[:3]:
            _, mul, inv = lib.semidirect_group(m, k, r)
            out.append((mul, inv))
    return out


def _cost(N, T, invl, S, D):
    """Number of (source, vertex) pairs not reached within distance D from A_e and B_e."""
    Sinv = [invl[s] for s in S]
    twoN = 2 * N
    total = 0
    for src in (0, N):
        seen = bytearray(twoN)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = T[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = T[v - N]
                    for t in Sinv:
                        w = row[t]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += twoN - count
    return total


def _climb(e, steps, rng, N, D, d):
    T, invl, S, cost = e
    inS = set(S)
    for _ in range(steps):
        if cost == 0:
            break
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in inS:
            continue
        S2 = S[:]
        S2[i] = g
        c2 = _cost(N, T, invl, S2, D)
        if c2 <= cost or rng.random() < 0.01:
            inS.discard(S[i])
            inS.add(g)
            S, cost = S2, c2
    e[2] = S
    e[3] = cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 5.0)
    deadline = start + max(budget, 0.5)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, always valid

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    rng = random.Random(seed)
    best = None  # (N, T, S)
    N = d + 1
    while time.monotonic() < deadline:
        prepared = []
        for mul, inv in _groups(N, rng):
            if time.monotonic() >= deadline:
                break
            T = _table(N, mul)
            invl = [inv(x) for x in range(N)]
            S = rng.sample(range(N), d)
            cost = _cost(N, T, invl, S, D)
            prepared.append([T, invl, S, cost])
        if not prepared:
            break

        found = None
        for e in prepared:
            if e[3] == 0:
                found = e
                break
        while found is None and time.monotonic() < deadline:
            for e in prepared:
                if time.monotonic() >= deadline:
                    break
                _climb(e, 150, rng, N, D, d)
                if e[3] == 0:
                    found = e
                    break
        if found is None:
            break
        best = (N, found[0], found[2])
        N += 1

    if best is None:
        return fallback
    N, T, S = best
    edges = [(x, N + T[x][s]) for x in range(N) for s in S]
    n = 2 * N
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
