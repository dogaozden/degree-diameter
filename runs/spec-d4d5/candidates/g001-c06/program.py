import math
import random
import time

import lib


GCAP = 400          # cap on group order (tables are G x G)
_TABLE_CACHE = {}


def _moore(d, D):
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _group_options(G):
    """All (m, k, r) with Z_m x| Z_k of order G = m*k (k = 1 gives the cyclic group)."""
    opts = []
    for kk in range(1, G + 1):
        if G % kk:
            continue
        m = G // kk
        if kk == 1:
            opts.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                opts.append((m, kk, r))
    return opts


def _tables(m, k, r):
    """Multiplication table of the group (cached, bounded size)."""
    key = (m, k, r)
    t = _TABLE_CACHE.get(key)
    if t is None:
        order, mul, _inv = lib.semidirect_group(m, k, r)
        mt = [[mul(x, y) for y in range(order)] for x in range(order)]
        t = mt
        if len(_TABLE_CACHE) > 48:
            _TABLE_CACHE.clear()
        _TABLE_CACHE[key] = t
    return t


def _edges(k, G, darts, mt):
    """Bi-Cayley lift: dart (i, j, s) joins A_i,x to B_j,x*s for every x in the group."""
    E = []
    for i, j, s in darts:
        for x in range(G):
            E.append((i * G + x, (k + j) * G + mt[x][s]))
    return 2 * k * G, E


def _cost(k, G, D, darts, mt):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid.

    Left translation is an automorphism, so one representative per base copy suffices.
    """
    big = 10 ** 9
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return big
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ai = i * G
        bj = (k + j) * G
        for x in range(G):
            a = ai + x
            b = bj + mt[x][s]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _anneal(k, G, d, D, mt, rng, deadline, iters):
    """Anneal voltages and per-layer base permutations; returns darts with zero cost or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cur = _cost(k, G, D, darts, mt)
    T0, T1 = 3.0, 0.1
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, mt)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, mt)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = [None, None]

    def offer(n, e):
        if best[0] is None or n > best[0]:
            if lib.is_valid(n, e, d, D):
                best[0], best[1] = n, e

    # Safe fallbacks: K_{d,d} (diameter 2), and the even cycle C_{2D} for d = 2.
    offer(*lib.haar_graph(d, range(d)))
    if d == 2:
        offer(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])

    moore = _moore(d, D)

    # Projective plane incidence meets the Moore bound when D = 3 and d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        offer(*lib.projective_plane_incidence(d - 1))

    # Main search: bi-Cayley lifts over semidirect products with k base vertices per side.
    ks = [1, 2, 3]
    while time.monotonic() < deadline and best[0] < moore:
        cands = []
        for k in ks:
            gmax = min(GCAP, moore // (2 * k))
            lo = max(d, best[0] // (2 * k) + 1)
            for G in range(lo, min(gmax, lo + 3) + 1):
                cands.append((k, G))
        if not cands:
            break
        k, G = rng.choice(cands)
        opts = _group_options(G)
        if not opts:
            continue
        m_, k_, r_ = rng.choice(opts)
        mt = _tables(m_, k_, r_)
        darts = _anneal(k, G, d, D, mt, rng, deadline, 2500)
        if darts is not None:
            n, e = _edges(k, G, darts, mt)
            offer(n, e)

    return best[0], best[1]
