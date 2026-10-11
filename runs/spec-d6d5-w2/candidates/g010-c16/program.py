"""Voltage-lift search with a degree-deficient lift and greedy completion.

New idea in this version: for a target (d, D), also search lifts whose
per-vertex degree is d-1 instead of d. Annealing finds voltages that give
diameter D up to a few bad pairs. Then a greedy completion adds the spare
degree (one extra edge per vertex) between deficient opposite-side vertices,
choosing among sampled candidates by the exact bad-pair count. Adding an edge
never increases the bad-pair count, so the completed graph keeps the lift's
validity guarantees and gains a near-perfect matching of extra edges.
"""
import math
import random
import time

import lib


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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
# Left block A_i = i*G + g, right block B_j = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j, g*s for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_K2_POOL = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
_COMP_MAX = 40


def _sample_group(G, rng, choices):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(choices)
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Sum over block representatives of vertices not reached within D. Zero means valid."""
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(dl, k, G, rng):
    darts = []
    for _ in range(dl):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _anneal(dl, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and B-endpoints of a lift with dl darts per block. Returns (darts, perms, cost)."""
    darts = _random_darts(dl, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(dl)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, perms, cost


# ----------------------------------------------------------------------------
# Exact bad-pair counting and greedy degree completion.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance more than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _complete(n, E, split, d, D, deadline, rng):
    """Add edges between deficient opposite-side vertices (vertices < split are left).

    Each step samples a few candidate right partners for a random deficient left
    vertex and keeps the one with the fewest bad pairs. Adding edges never
    increases the bad count, so this only improves validity. Returns (E, bad).
    """
    E = list(E)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    bad = _bad_count(n, adj, D)
    tries = 0
    while bad > 0 and time.monotonic() < deadline and tries < 4 * n:
        tries += 1
        L = [v for v in range(split) if len(adj[v]) < d]
        R = [v for v in range(split, n) if len(adj[v]) < d]
        if not L or not R:
            break
        a = rng.choice(L)
        best = None
        for _ in range(3):
            b = rng.choice(R)
            if (min(a, b), max(a, b)) in existing:
                continue
            adj[a].append(b)
            adj[b].append(a)
            c = _bad_count(n, adj, D)
            adj[a].pop()
            adj[b].pop()
            if best is None or c < best[0]:
                best = (c, b)
            if time.monotonic() >= deadline:
                break
        if best is None:
            continue
        c, b = best
        adj[a].append(b)
        adj[b].append(a)
        existing.add((min(a, b), max(a, b)))
        E.append((a, b))
        bad = c
    return E, bad


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Lift search with direct (degree d) and completed (degree d-1 plus greedy edges) modes.
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 6)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, _K2_POOL)
        if g is None:
            continue
        order, mul = g

        use_comp = d >= 3 and rng.random() < 0.5
        dl = d - 1 if use_comp else d
        iters = 600 if k == 1 else 300
        darts, perms, cost = _anneal(dl, D, k, order, mul, rng, deadline, iters)
        N, E = _edges(k, order, darts, perms)

        if cost == 0:
            consider(N, E)
        elif use_comp and cost <= _COMP_MAX and time.monotonic() < deadline:
            comp_end = min(deadline, time.monotonic() + 12.0)
            E2, bad = _complete(N, E, k * order, d, D, comp_end, rng)
            if bad == 0:
                consider(N, E2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
