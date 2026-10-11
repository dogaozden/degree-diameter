import math
import random
import time

import lib

_BIG = 10 ** 9


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random group of order G: Z_m x| Z_k2 with m * k2 = G. Returns (order, mul) or None."""
    options = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not options:
        return None
    k2 = rng.choice(options)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [x for x in range(1, m)
                 if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul


def _random_darts(d, k, G, rng):
    """d layers; each layer is a random permutation p of range(k) giving darts (i, p[i], s)."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _cost(k, G, D, darts, perm_of, limit=None):
    """Unreached (representative, vertex) pairs at distance > D. Zero means valid.

    The lift is invariant under left multiplication by the group, so one
    representative per base vertex suffices. Returns early once total > limit.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = perm_of(s)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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
        if limit is not None and total > limit:
            return total
    return total


def _edges(k, G, darts, perm_of):
    E = set()
    for i, j, s in darts:
        pm = perm_of(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Annealing with plateau-friendly Metropolis acceptance over voltages and layer permutations."""
    cache = {}

    def perm_of(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    darts = _random_darts(d, k, G, rng)
    cost = _cost(k, G, D, darts, perm_of)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, perm_of, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perm_of, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost == 0, darts, cost, perm_of


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        # Even cycle C_{2D} has diameter D and max degree 2.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts over small groups, annealed toward diameter D.
    if D >= 3 and time.monotonic() < deadline:
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            lo = best_n // (2 * k) + 1
            hi = lo + max(4, lo // 10)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            iters = 3000 if k == 1 else 1000
            ok, darts, _, perm_of = _anneal(d, D, k, order, mul, rng, deadline, iters)
            if ok:
                n, e = _edges(k, order, darts, perm_of)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
