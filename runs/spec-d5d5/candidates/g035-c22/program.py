import math
import random
import time

import lib


_BIG = 10 ** 6


def _rot(X, s, N, full):
    """Bitset of {x + s mod N : x in X}."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & full


def _cost(k, N, d, D, p, sh):
    """Number of (representative, vertex) pairs at distance > D in the lift; 0 means valid.

    Base: k A-orbits and k B-orbits, layer l joins A_i to B_{p[l][i]} with voltage sh[l][i].
    The lift has vertex set Z_N per orbit; translations act transitively on each orbit,
    so one BFS per orbit suffices.
    """
    # Multi-edge check: same (target, voltage) twice from one A-orbit is a duplicate edge.
    for i in range(k):
        seen = set()
        for l in range(d):
            key = (p[l][i], sh[l][i])
            if key in seen:
                return _BIG
            seen.add(key)

    full = (1 << N) - 1
    nb = [[] for _ in range(2 * k)]
    for l in range(d):
        pl = p[l]
        sl = sh[l]
        for i in range(k):
            j = pl[i]
            s = sl[i]
            nb[i].append((k + j, s))
            nb[k + j].append((i, (N - s) % N))

    total = 0
    m2 = 2 * k
    for o in range(m2):
        vis = [0] * m2
        fr = [0] * m2
        vis[o] = 1
        fr[o] = 1
        for _ in range(D):
            new = [0] * m2
            for q in range(m2):
                f = fr[q]
                if f:
                    for t, s in nb[q]:
                        new[t] |= _rot(f, s, N, full)
            active = False
            for q in range(m2):
                x = new[q] & ~vis[q] & full
                new[q] = x
                vis[q] |= x
                if x:
                    active = True
            fr = new
            if not active:
                break
        for q in range(m2):
            total += N - vis[q].bit_count()
    return total


def _anneal(k, N, d, D, rng, iters, deadline):
    """Simulated annealing over per-layer permutations and voltages. Returns (p, sh) or None."""
    p = [rng.sample(range(k), k) for _ in range(d)]
    sh = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
    cost = _cost(k, N, d, D, p, sh)
    T0 = 3.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.05
        l = rng.randrange(d)
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = sh[l][i]
            new = rng.randrange(N)
            if new == old:
                continue
            sh[l][i] = new
            c2 = _cost(k, N, d, D, p, sh)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                sh[l][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            pl = p[l]
            pl[a], pl[b] = pl[b], pl[a]
            c2 = _cost(k, N, d, D, p, sh)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                pl[a], pl[b] = pl[b], pl[a]
    if cost == 0:
        return p, sh
    return None


def _edges(k, N, d, p, sh):
    """Expand the base lift into an explicit edge list on 2kN vertices."""
    E = set()
    for l in range(d):
        for i in range(k):
            j = p[l][i]
            s = sh[l][i]
            for g in range(N):
                E.add((i * N + g, (k + j) * N + (g + s) % N))
    return 2 * k * N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    # Structured baseline for D = 3: incidence graph of PG(2, d-1) when d-1 is a prime power.
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n3, e3 = lib.projective_plane_incidence(d - 1)
        if n3 > best[0] and lib.is_valid(n3, e3, d, D):
            best = (n3, e3)

    # Main search: cyclic multi-orbit lifts (bi-Cayley style) with annealing.
    # Each attempt aims for an order just above the current best.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        ks = [k for k in range(1, 7) if 2 * k * (n_best // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        lo = n_best // (2 * k) + 1
        N = lo + rng.randrange(0, 3)
        if 2 * k * N > moore or N < d:
            continue
        res = _anneal(k, N, d, D, rng, 4000, deadline)
        if res is not None:
            p, sh = res
            n2, e2 = _edges(k, N, d, p, sh)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
