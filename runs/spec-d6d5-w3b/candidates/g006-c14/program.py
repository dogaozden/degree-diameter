import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence and Araujo-Pardo-Lopez (D = 3).
# Everything else is a fallback chain, so every case returns a valid graph.
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
# New main family: tabu-searched bi-Cayley voltage lifts over semidirect
# products Z_m x| Z_k2, with a base of k A-vertices and k B-vertices per group
# element. Each layer L is a perfect matching of A-indices to B-indices, and
# every dart (i, j, s) joins A_{i,g} to B_{j,g*s}. Each A-vertex gets exactly
# one edge per layer, so the lift is d-regular and bipartite by construction.
#
# Search: tabu search over two move types (re-roll one voltage, swap two
# B-targets inside one layer) minimizing the number of vertex pairs at
# distance > D, measured from one representative per base vertex.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng, k2_choices):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for L in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _tabu_lift(d, D, k, G, mul, rng, deadline, max_iter):
    """Tabu search over voltages and layer matchings. Returns (n, edges) or None."""
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    best_cost = cost
    best = [list(x) for x in darts]
    tabu = {}
    stall = 0
    it = 0
    nd = len(darts)

    while cost > 0 and it < max_iter and time.monotonic() < deadline:
        it += 1
        mv_best = None
        for _ in range(12):
            if k == 1 or rng.random() < 0.6:
                idx = rng.randrange(nd)
                old = darts[idx][2]
                new = rng.randrange(G)
                if new == old:
                    continue
                darts[idx][2] = new
                perms[idx] = _right_perm(mul, G, new)
                c = _cost(k, G, D, darts, perms)
                darts[idx][2] = old
                perms[idx] = _right_perm(mul, G, old)
                key = ("v", idx)
                mv = ("v", idx, new)
            else:
                L = rng.randrange(d)
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                c = _cost(k, G, D, darts, perms)
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                key = ("p", ia, ib)
                mv = ("p", ia, ib)
            if tabu.get(key, -1) > it and c >= best_cost:
                continue
            if mv_best is None or c < mv_best[0]:
                mv_best = (c, mv, key)

        if mv_best is None:
            continue
        c, mv, key = mv_best
        if mv[0] == "v":
            _, idx, new = mv
            darts[idx][2] = new
            perms[idx] = _right_perm(mul, G, new)
        else:
            _, ia, ib = mv
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        tabu[key] = it + rng.randint(3, 8)
        cost = c
        if cost < best_cost:
            best_cost = cost
            best = [list(x) for x in darts]
            stall = 0
        else:
            stall += 1
        if stall > 300:
            darts = _random_darts(d, k, G, rng)
            perms = [_right_perm(mul, G, s) for _, _, s in darts]
            cost = _cost(k, G, D, darts, perms)
            tabu = {}
            stall = 0

    if best_cost != 0:
        return None
    perms = [_right_perm(mul, G, s) for _, _, s in best]
    return _edges(k, G, best, perms)


# ----------------------------------------------------------------------------
# Build: safe fallbacks first, then the lift search for D >= 4.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and d >= 3:
        rng = random.Random(seed * 104729 + d * 31 + D)
        ks = [1, 1, 2, 2, 3]
        k2_pool = [1, 2, 2, 3, 4, 5, 6, 8, 10, 12]
        while time.monotonic() < deadline - 1.0 and best_n < moore:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            lo = max(2, base + 1)
            hi = lo + max(3, lo // 10)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng, k2_pool)
            if g is None:
                continue
            order, mul = g
            now = time.monotonic()
            slice_end = min(deadline, now + 8.0)
            res = _tabu_lift(d, D, k, order, mul, rng, slice_end, 600)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
