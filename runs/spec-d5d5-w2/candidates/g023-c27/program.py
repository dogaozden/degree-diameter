import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

_PEN = 25        # penalty per duplicated dart (same base pair and voltage)
RUN_SECS = 6.0   # wall-clock cap per annealing run
ITERS = 1500     # annealing steps per run


# ----------------------------------------------------------------------------
# Baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, searched by annealing.
#
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. Each of the d layers
# L is a perfect matching i -> perms[L][i] between A-base and B-base vertices,
# with a voltage vol[L][i] in the group. The lift has vertices (side, base, g)
# and edges A_{i,g} -- B_{perms[L][i], g*vol[L][i]} for every layer L and g.
#
# Left multiplication is an automorphism of the lift, so the eccentricities of
# the 2k representatives (identity of each base vertex) decide the diameter.
# Evaluation is a bitset ball expansion over the whole lift, with duplicated
# darts penalized rather than forbidden so the walk can move through them.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """Semidirect parameters (m, k, r) with m * k = G, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _eval(k, G, d, D, perms, vol, rtab):
    """Return (cost, dups). cost == 0 exactly when the lift is a valid candidate."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen = set()
    dups = 0
    for L in range(d):
        p = perms[L]
        for i in range(k):
            j = p[i]
            s = vol[L][i]
            key = (i, j, s)
            if key in seen:
                dups += 1
                continue
            seen.add(key)
            R = rtab(s)
            ai = i * G
            bj = (k + j) * G
            for g in range(G):
                a = ai + g
                b = bj + R[g]
                adj[a].append(b)
                adj[b].append(a)

    # Bitset ball expansion: reach[v] holds all vertices within distance t of v.
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new

    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    bad = sum(N - reach[v].bit_count() for v in reps)
    return bad + _PEN * dups, dups


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and layer matchings until every representative reaches all within D."""
    table = [None] * G

    def rtab(s):
        t = table[s]
        if t is None:
            t = [mul(g, s) for g in range(G)]
            table[s] = t
        return t

    perms = [rng.sample(range(k), k) for _ in range(d)]
    vol = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cost, _ = _eval(k, G, d, D, perms, vol, rtab)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = vol[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            vol[L][i] = new
            c2, _ = _eval(k, G, d, D, perms, vol, rtab)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                vol[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            p = perms[L]
            p[a], p[b] = p[b], p[a]
            c2, _ = _eval(k, G, d, D, perms, vol, rtab)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]

    if cost != 0:
        return None
    edges = set()
    for L in range(d):
        for i in range(k):
            j = perms[L][i]
            R = rtab(vol[L][i])
            for g in range(G):
                edges.add((i * G + g, (k + j) * G + R[g]))
    return 2 * k * G, sorted(edges)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D, and meets the Moore bound 2D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Ladder search: each success raises the bar, so the group order climbs.
    while best[0] < moore and time.monotonic() < deadline:
        best_n = best[0]
        ks = [k for k in (1, 2, 3) if 2 * k * (best_n // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(0, max(2, lo // 12))
        m, k2, r = rng.choice(_groups_of_order(G))
        order, mul, _ = lib.semidirect_group(m, k2, r)
        run_deadline = min(deadline, time.monotonic() + RUN_SECS)
        res = _anneal(d, D, k, order, mul, rng, run_deadline, ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
