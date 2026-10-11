import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3), used for D >= 3 when it fits.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Each "layer" L (of d layers) is a permutation p_L of range(k) and gives
# darts (i, p_L[i], s) joining A_i,g to B_{p_L[i]}, g*s for all g.
# Every A and B vertex then has degree exactly d.
#
# Left multiplication by a group element is an automorphism, so distances
# only need to be checked from one representative per (side, layer).
#
# Distinct search from the earlier version: the cost is the exact number of
# bad pairs from representatives, computed with big-integer bitset
# propagation over all vertices at once, and the move set mixes voltage
# changes with target swaps inside a layer.
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


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    seen = set()
    for dart in darts:
        key = (dart[0], dart[1], dart[2])
        if key in seen:
            return _BIG
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        changed = False
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
            if x != reach[v]:
                changed = True
        reach = new
        if not changed:
            break
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    bad = 0
    for src in reps:
        bad += N - reach[src].bit_count()
    return bad


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target permutations."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = (2.0 + 0.05 * cost) if cost < _BIG else 5.0
    T_end = 0.3
    decay = (T_end / T) ** (1.0 / max(1, iters)) if T > T_end else 1.0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if k == 1 or rng.random() < 0.75:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing more to gain (e.g. the d3D3 calibration).
    moore = lib._moore_bound(d, D)
    if best_n >= moore or D < 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Bi-Cayley voltage lifts over semidirect products, targeting orders above the best so far.
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        if best_n >= moore:
            break
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 4))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=1500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
