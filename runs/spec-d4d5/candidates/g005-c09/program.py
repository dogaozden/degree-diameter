import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold family: edge-swap simulated annealing on d-regular bipartite graphs.
#
# Start from a Haar graph (d distinct shifts on Z_m), so every vertex has
# degree exactly d. Each move swaps the endpoints of two edges (a1,b1),(a2,b2)
# into (a1,b2),(a2,b1), which keeps all degrees fixed. The cost is the number
# of vertex pairs at distance > D. Stop at cost 0.
# ----------------------------------------------------------------------------

def _bad_pairs_edges(n, E, D):
    """Number of unordered vertex pairs at distance > D (bitmask ball growth)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        changed = False
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            if r != reach[v]:
                changed = True
            new.append(r)
        reach = new
        if not changed:
            break
    return sum(n - r.bit_count() for r in reach) // 2


def _sa_regular(m, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on parts of size m; return (n, edges) or None."""
    n = 2 * m
    shifts = rng.sample(range(m), d)
    E = [(i, m + (i + s) % m) for i in range(m) for s in shifts]
    S = set(E)
    cost = _bad_pairs_edges(n, E, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T_hi, T_lo = 1.5, 0.15
    L = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T_hi * (T_lo / T_hi) ** min(1.0, (now - t0) / span)
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in S or e2 in S:
            continue
        E[i] = e1
        E[j] = e2
        c2 = _bad_pairs_edges(n, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add(e1)
            S.add(e2)
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return (n, list(E)) if cost == 0 else None


# ----------------------------------------------------------------------------
# Secondary family: annealed Z_m x| Z_k voltage lifts (bi-Cayley graphs).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Pairs (representative, vertex) not reached within D. Zero means valid."""
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
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

    if d == 2:
        # Even cycle C_{2D} is bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    if D == 2:
        return best_n, best_e

    # Projective plane base (diameter 3).
    pg = _pg_base(d)
    if pg is not None:
        consider(pg[0], pg[1])

    moore = 2 * sum((d - 1) ** i for i in range(D))
    if best_n >= moore:
        return best_n, best_e

    total = deadline - start
    group_end = start + 0.35 * total

    # Phase A: annealed group voltage lifts.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < group_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, group_end, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Phase B: edge-swap annealing on d-regular bipartite graphs, one part larger
    # than the current best. Restart with a fresh start when a slice runs out.
    while time.monotonic() < deadline - 0.5:
        m = best_n // 2 + 1
        now = time.monotonic()
        slice_end = min(deadline, now + max(4.0, 0.5 * (deadline - now)))
        res = _sa_regular(m, d, D, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
