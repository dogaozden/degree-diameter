"""Bi-Cayley and multi-base voltage-lift search for bipartite graphs of max degree d and diameter D.

Construction: A_x ~ B_{x*g} for g in S over semidirect groups Z_m x| Z_k (bi-Cayley lifts,
searched by annealing a connection set S with 0 in S), plus k-base-vertex lifts (k = 2, 3)
searched by annealing voltages and layer permutations. Every candidate is checked with
lib.is_valid before it replaces the best graph, and K_{d,d} is the fallback.
Untested in this form: correctness is enforced by is_valid, not by a run.
"""
import math
import random
import time

import lib

_TABLE_CACHE = {}
_BIG = 10 ** 9
MAX_GROUPS = 6
CLIMB_ITERS = 400
ANNEAL_ITERS = 1500
BAND = 6


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, T, invs): T[x][g] = x*g, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached_bi(N, T, invs, S, D):
    """Pairs not within distance D, counted from A_0 and B_0 (left translation is an automorphism)."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _bicayley_search(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (0 in S WLOG) to zero unreached pairs; None on failure."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached_bi(N, T, invs, S, D)
    temp = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached_bi(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
        temp = max(0.3, temp * 0.995)
    return S if cur == 0 else None


def _multi_cost(k, G, T, darts, D):
    """Unreached (rep, vertex) pairs for a k-base lift. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ai = i * G
        bj = (k + j) * G
        for g in range(G):
            a = ai + g
            b = bj + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _multi_search(d, D, k, G, T, rng, deadline, iters):
    """Anneal voltages and per-layer permutations; returns darts with cost 0, or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _multi_cost(k, G, T, darts, D)
    temp = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, temp * 0.997)
        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _multi_cost(k, G, T, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _multi_cost(k, G, T, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts if cost == 0 else None


def _multi_edges(k, G, T, darts):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + T[g][s]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2: safe fallback
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n2, e2 = lib.projective_plane_incidence(q)
                consider(n2, e2)
                break

    rng = random.Random(seed * 1000003 + 97 * d + D)

    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        if rng.random() < 0.65:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            N = min(lo + rng.randrange(BAND), moore // 2)
            if N < d:
                continue
            groups = _groups(N)
            rng.shuffle(groups)
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, T, invs = _tables(m, k2, r)
                S = _bicayley_search(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                    consider(2 * N, edges)
                    break
        else:
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            G = lo + rng.randrange(BAND)
            if 2 * k * G > moore or G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            _, T, _ = _tables(m, k2, r)
            darts = _multi_search(d, D, k, G, T, rng, deadline, ANNEAL_ITERS)
            if darts is not None:
                n2, e2 = _multi_edges(k, G, T, darts)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
