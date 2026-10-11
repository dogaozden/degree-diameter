import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured small-D families (instant, used as the initial incumbent).
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (q capped for speed)."""
    for q in range(min(d - 1, 23), 1, -1):
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


def _moore_bipartite(d, D):
    """Bipartite Moore bound 2 * sum_{i<D} (d-1)^i (valid for d >= 3)."""
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, with k base vertices
# per side and d darts per base vertex (one dart per "layer").
#
# Vertices: A_{i,g} = i*G + g,  B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every group element g.
# Layer L is a permutation sigma_L of range(k): dart (i, sigma_L(i), s).
# Every A and every B then has degree exactly d.
#
# Left multiplication by any h is an automorphism, so the 2k block identities
# are the only sources that need checking. A lift has diameter <= D iff every
# block identity reaches all 2kG vertices within D steps.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G; returns (order, mul) or None."""
    for _ in range(60):
        k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
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
    """Number of (block identity, vertex) pairs at distance > D. Zero iff the lift is valid.

    Returns early with a value above `limit` once the running total exceeds it.
    Parallel darts (identical (i, j, s)) give _BIG.
    """
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    keys = set()
    for (i, j, s), pm in zip(darts, perms):
        key = (i, j, s)
        if key in keys:
            return _BIG
        keys.add(key)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    sources = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in sources:
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
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
    """Metropolis annealing over voltages and layer permutations. Returns (darts, perms, cost)."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())

        if k > 1 and rng.random() < 0.25:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        else:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            old_p = perms[idx]
            darts[idx][2] = new
            perms[idx] = _right_perm(mul, G, new)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = old_p
    return darts, perms, cost


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + min(0.85 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration cases already at the Moore bound return immediately.
    if D >= 3 and best_n >= _moore_bipartite(d, D):
        return best

    # Bi-Cayley lift search (D >= 3). Each success raises the bar, so the
    # group orders keep climbing above the incumbent.
    if D >= 3:
        while time.monotonic() < hard:
            k = rng.choice([1, 1, 2, 2, 3])
            gmin = best_n // (2 * k) + 1
            G = gmin + rng.randint(0, max(2, gmin // 12))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            trial_deadline = min(hard, time.monotonic() + 6.0)
            darts, perms, c = _anneal(d, D, k, order, mul, rng,
                                      trial_deadline, 1500)
            if c == 0:
                n, e = _edges(k, order, darts, perms)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
