import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d} (diameter 2) and the projective-plane incidence graph
# (diameter 3, degree q+1 for the largest prime power q <= d-1).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (order G),
# base graph with k vertices per side and d layers of permutation darts.
#
# Vertex block i (0..k-1) is A_i, block k+j is B_j. Dart (i, j, s) joins
# A_i,g to B_j,mul(g,s) for all g. Each layer is a bijection i -> j, so the
# lift is d-regular and bipartite.
#
# Search objective: number of ordered vertex pairs at distance > D, computed
# with big-int bitmask ball propagation over the whole lift. Zero means valid.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    if G < 3:
        return None
    k2s = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 3]
    if not k2s:
        return None
    k2 = rng.choice(k2s)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in range(2, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        out[rng.randrange(len(out))][2] = rng.randrange(G)
    return out


def _bad_pairs_ordered(N, adj, D):
    """Sum over vertices of the number of vertices NOT within distance D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _cost(k, G, perm, darts, D):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG  # duplicate darts would create duplicate edges
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ps = perm[s]
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + ps[g]
            adj[a].append(b)
            adj[b].append(a)
    return _bad_pairs_ordered(N, adj, D)


def _edges(k, G, perm, darts):
    E = []
    for i, j, s in darts:
        ps = perm[s]
        for g in range(G):
            E.append((i * G + g, (k + j) * G + ps[g]))
    return 2 * k * G, E


def _anneal(k, d, G, perm, D, rng, darts, deadline):
    """Greedy-ish annealing over voltages and per-layer B-assignments.

    Returns (cost, darts). cost == 0 means the lift is valid.
    """
    cost = _cost(k, G, perm, darts, D)
    T = 4.0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.2, T * 0.999)
        limit = cost - T * math.log(1.0 - rng.random())
        if k > 1 and rng.random() < 0.3:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, perm, darts, D)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        else:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            c2 = _cost(k, G, perm, darts, D)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
    return cost, darts


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = [lib.haar_graph(d, range(d))[0], lib.haar_graph(d, range(d))[1]]
    best[0] = d * 2

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    best[1] = lib.haar_graph(d, range(d))[1]

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing to search for (e.g. d=3, D=3 -> 14).
    if best[0] >= lib._moore_bound(d, D):
        return best[0], best[1]

    # Main search: annealed bi-Cayley lifts over semidirect products.
    attempt_secs = max(2.0, 0.12 * time_limit)
    elite = {}  # (k, G) -> (cost, darts)
    while time.monotonic() < deadline - 0.5:
        best_n = best[0]
        k = rng.choice([1, 1, 1, 2, 2, 3])
        gmin = best_n // (2 * k) + 1
        window = max(2, gmin // 12)
        G = rng.randint(gmin, gmin + window)

        grp = _sample_group(G, rng)
        if grp is None:
            continue
        order, mul = grp
        perm = [[mul(g, s) for g in range(order)] for s in range(order)]

        key = (k, order)
        if key in elite and rng.random() < 0.5:
            darts = _perturb(elite[key][1], order, rng, rng.randint(1, 3))
        else:
            darts = _random_darts(d, k, order, rng)

        attempt_end = min(deadline, time.monotonic() + attempt_secs)
        cost, darts = _anneal(k, d, order, perm, D, rng, darts, attempt_end)

        if cost == 0:
            n, e = _edges(k, order, perm, darts)
            consider(n, e)
        else:
            if key not in elite or cost < elite[key][0]:
                elite[key] = (cost, [list(x) for x in darts])

    if not lib.is_valid(best[0], best[1], d, D):
        fb = lib.haar_graph(d, range(d))
        return fb[0], fb[1]
    return best[0], best[1]
