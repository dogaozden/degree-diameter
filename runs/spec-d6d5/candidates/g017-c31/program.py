import math
import random
import time

import lib

_BIG = 10 ** 6


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random group of order G: cyclic Z_G or a semidirect product Z_m x| Z_k2. Returns (order, mul) or None."""
    ks = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 3]
    if not ks:
        return None
    rng.shuffle(ks)
    for k2 in ks:
        m = G // k2
        if k2 == 1:
            order, mul, _ = lib.cyclic_group(m)
            return order, mul
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            order, mul, _ = lib.semidirect_group(m, k2, rs[rng.randrange(len(rs))])
            return order, mul
    return None


def _right_perm(order, mul):
    """Return get(s) giving the permutation g -> mul(g, s), cached per s."""
    cache = {}

    def get(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(order)]
            cache[s] = p
        return p

    return get


def _darts(k, layers):
    """Flatten layers into darts (i, j, s): block A_i joins block B_j through voltage s."""
    return [(i, p[i], v[i]) for p, v in layers for i in range(k)]


def _cost(k, G, D, darts, get_perm, limit):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid.

    The group acts by left translation on each block, so one BFS per block
    (from its identity element) is enough. Returns early once total > limit.
    """
    if len(set(darts)) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        p = get_perm(s)
        ai, bj = i * G, (k + j) * G
        for g in range(G):
            a, b = ai + g, bj + p[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for blk in list(range(k)) + [k + j for j in range(k)]:
        src = blk * G
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, get_perm):
    E = set()
    for i, j, s in darts:
        p = get_perm(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + p[g]))
    return 2 * k * G, sorted(E)


def _random_layers(k, d, G, rng):
    layers = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        v = [rng.randrange(G) for _ in range(k)]
        layers.append([p, v])
    return layers


def _anneal(k, d, D, G, get_perm, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer block matchings.

    Returns (final_cost, layers). Cost zero means a valid bi-Cayley lift.
    """
    layers = _random_layers(k, d, G, rng)
    cur = _cost(k, G, D, _darts(k, layers), get_perm, float("inf"))
    T = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.997)
        limit = cur - T * math.log(1.0 - rng.random())
        p, v = layers[rng.randrange(d)]
        if k > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(k), 2)
            p[a], p[b] = p[b], p[a]
            c2 = _cost(k, G, D, _darts(k, layers), get_perm, limit)
            if c2 <= limit:
                cur = c2
            else:
                p[a], p[b] = p[b], p[a]
        else:
            i = rng.randrange(k)
            old = v[i]
            v[i] = rng.randrange(G)
            c2 = _cost(k, G, D, _darts(k, layers), get_perm, limit)
            if c2 <= limit:
                cur = c2
            else:
                v[i] = old
    return cur, layers


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3 and d >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts over groups of order near the current target.
    # k = 1 gives 2G vertices, k = 2 gives 4G vertices. Each lift is d-regular.
    if D >= 3:
        while time.monotonic() < deadline:
            k = 1 if rng.random() < 0.6 else 2
            G = best_n // (2 * k) + 1 + rng.randint(0, 3)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            get_perm = _right_perm(order, mul)
            iters = 2500 if k == 1 else 1000
            cur, layers = _anneal(k, d, D, order, get_perm, rng, deadline, iters)
            if cur == 0:
                n, e = _edges(k, order, _darts(k, layers), get_perm)
                consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
