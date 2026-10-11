import math
import random
import time

import lib


_BIG = 10 ** 9


def _moore(d, D):
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k, annealed (parent family).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _vcost(k, G, D, darts, perms):
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


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _vanneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: double-edge-swap annealing on d-regular bipartite graphs.
#
# Start from a random Haar graph (d-regular, bipartite, simple) on m + m
# vertices and apply degree-preserving double-edge swaps
#     (a1,b1),(a2,b2)  ->  (a1,b2),(a2,b1)
# which keep the graph simple, d-regular and bipartite. The cost is the
# number of ordered vertex pairs at distance more than D, computed with
# bitmask balls. Simulated annealing accepts or reverts each swap.
# A swap is its own inverse, so reverting uses the same routine.
# ----------------------------------------------------------------------------

def _bad_pairs_adj(adj, n, D):
    """Ordered pairs at distance > D, from bitmask balls over adjacency lists."""
    reach = [1 << v for v in range(n)]
    full = (1 << n) - 1
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if all(r == full for r in reach):
            return 0
    return sum(n - r.bit_count() for r in reach)


def _swap_pair(adj, a1, i1, a2, i2):
    """Exchange the B-neighbours at slot i1 of a1 and slot i2 of a2 (self-inverse)."""
    x = adj[a1][i1]
    y = adj[a2][i2]
    adj[a1][i1] = y
    adj[a2][i2] = x
    j = adj[x].index(a1)
    adj[x][j] = a2
    j = adj[y].index(a2)
    adj[y][j] = a1


def _swap_anneal(m, d, D, rng, deadline):
    """Find a d-regular bipartite graph on m + m vertices with diameter <= D, or None."""
    n = 2 * m
    adj = [[] for _ in range(n)]
    shifts = rng.sample(range(m), d)
    for a in range(m):
        for s in shifts:
            b = m + (a + s) % m
            adj[a].append(b)
            adj[b].append(a)
    cost = _bad_pairs_adj(adj, n, D)
    if cost == 0:
        return adj

    T0 = max(2.0, 0.02 * cost)
    T1 = 0.2
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        a1 = rng.randrange(m)
        a2 = rng.randrange(m)
        if a1 == a2:
            continue
        i1 = rng.randrange(d)
        i2 = rng.randrange(d)
        b1 = adj[a1][i1]
        b2 = adj[a2][i2]
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        _swap_pair(adj, a1, i1, a2, i2)
        c2 = _bad_pairs_adj(adj, n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return adj
        else:
            _swap_pair(adj, a1, i1, a2, i2)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = _moore(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and n <= moore and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        # Phase 1: annealed group voltage lifts (parent family), first 30% of the budget.
        if D >= 3 and d >= 3:
            vend = start + 0.3 * time_limit
            if D >= 5:
                ks = [1, 1, 2, 2, 3, 4]
                iters = 1500
            else:
                ks = [1, 1, 2, 3]
                iters = 400
            while time.monotonic() < vend and best_n < moore:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _vanneal(d, D, k, order, mul, rng, vend, iters)
                if res is not None:
                    consider(res[0], res[1])

        # Phase 2 (new): double-edge-swap annealing for balanced graphs of order 2m,
        # aiming just above the current best order and extending on each success.
        m = best_n // 2 + 1
        while time.monotonic() < deadline and 2 * m <= moore and m >= d:
            m = max(m, best_n // 2 + 1)
            ok = False
            tries = 0
            while not ok and tries < 6 and time.monotonic() < deadline:
                now = time.monotonic()
                budget = max(2.0, (deadline - now) * 0.35)
                adj = _swap_anneal(m, d, D, rng, min(deadline, now + budget))
                tries += 1
                if adj is not None:
                    ok = True
                    edges = [(a, b) for a in range(m) for b in adj[a]]
                    consider(2 * m, edges)
            if not ok:
                break
            m += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
