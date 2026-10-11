import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence graph and the Araujo-Pardo-Lopez
# graph for D = 3, plus K_{d,d} as the universal fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family for D >= 5: generalized bi-Cayley lifts over random groups.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, for g, h in the group.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g. Each layer L of d
# layers is a permutation p_L of the k orbits, with one voltage per orbit, so
# every vertex has degree d (duplicate edges only lower degree, never break
# validity).
#
# Left translation by any group element is an automorphism, so the diameter
# condition only needs BFS from the k A-representatives and the k B-
# representatives. The cost is the number of unreached (rep, vertex) pairs,
# and zero means diameter <= D.
#
# Search: simulated annealing over voltages and per-layer permutations, with
# groups Z_m x| Z_k2 chosen so that the order G is slightly above the
# current best. Any graph that passes lib.is_valid is kept.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul)."""
    divs = [k for k in range(1, min(G, 48) + 1) if G % k == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            pool = rng.sample(range(1, m), min(m - 1, 80))
            cands = [x for x in pool
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, row):
    """Number of (representative, vertex) pairs at distance more than D. Zero means valid."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        R = row(s)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + R[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in srcs:
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


def _edges(k, G, darts, row):
    """Full edge list of the lift, without duplicates."""
    E = set()
    for i, j, s in darts:
        R = row(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + R[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Anneal one lift over a fixed group. Returns (darts, row) on success, else None."""
    rows = {}

    def row(s):
        r = rows.get(s)
        if r is None:
            r = [mul(g, s) for g in range(G)]
            rows[s] = r
        return r

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cost = _cost(k, G, D, darts, row)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        saved = [x[:] for x in darts]
        if k == 1 or rng.random() < 0.6:
            darts[rng.randrange(len(darts))][2] = rng.randrange(G)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        c2 = _cost(k, G, D, darts, row)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts = saved
        T = max(0.05, T * 0.998)

    if cost == 0:
        return darts, row
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 5 and d >= 3:
        ks = [1, 1, 1, 2, 2, 3]
        while time.monotonic() < deadline and best_n < moore:
            k = rng.choice(ks)
            # Start near 0.35 * Moore (the record sits near 0.44 * Moore) and
            # move up as better graphs are found.
            lo = max(best_n // (2 * k) + 1, int(0.35 * moore / (2 * k)), 2)
            G = rng.randint(lo, lo + max(4, lo // 20))
            g = _random_group(G, rng)
            if g is None:
                continue
            order, mul = g
            iters = 700 if k == 1 else 300
            res = _search(d, D, k, order, mul, rng, deadline, iters)
            if res is not None:
                darts, row = res
                n, e = _edges(k, order, darts, row)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
