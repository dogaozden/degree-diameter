import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bitset distance counting. _bad returns the number of ordered vertex pairs
# at distance > D (zero means every pair is within distance D).
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# Family 1: annealed bi-Cayley voltage lifts over semidirect products.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s}. With k = 1 this is the bipartite
# double cover of a Cayley graph. Simple edges are obtained by deduplicating.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    opts = [k for k in (1, 2, 3, 4, 6, 8) if G % k == 0 and G // k >= 3]
    if not opts:
        return None
    k2 = rng.choice(opts)
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


def _right_perms(G, mul):
    return [[mul(g, s) for g in range(G)] for s in range(G)]


def _lift_bad(k, G, darts, R, D):
    n = 2 * k * G
    adj = [[] for _ in range(n)]
    for i, j, s in darts:
        pm = R[s]
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return _bad(n, adj, D)


def _lift_run(d, D, k, G, R, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _lift_bad(k, G, darts, R, D)
    T0 = max(2.0, 0.05 * cost)
    T_end = 0.3
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / iters)
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _lift_bad(k, G, darts, R, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_bad(k, G, darts, R, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return darts
    return None


def _lift_edges(k, G, darts, R):
    E = set()
    for i, j, s in darts:
        pm = R[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _group_phase(d, D, rng, deadline, best, consider):
    ks = [1, 1, 2] if D >= 5 else [1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        G = max(3, best["n"] // (2 * k) + 1 + rng.randrange(0, 2))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        R = _right_perms(order, mul)
        run_end = min(deadline, time.monotonic() + 6.0)
        darts = _lift_run(d, D, k, order, R, rng, run_end, 2500)
        if darts is not None:
            consider(*_lift_edges(k, order, darts, R))


# ----------------------------------------------------------------------------
# Family 2 (new): direct annealing over d-regular bipartite graphs.
# The graph is the union of d disjoint perfect matchings between sides
# A = 0..N-1 and B = N..2N-1. A move swaps the partners of two A vertices
# inside one matching. Cost = ordered pairs farther than D apart.
# ----------------------------------------------------------------------------

def _init_perms(N, d, rng):
    perms = []
    for _ in range(d):
        for _attempt in range(3000):
            p = list(range(N))
            rng.shuffle(p)
            if all(p[a] != q[a] for q in perms for a in range(N)):
                break
        else:
            return None
        perms.append(p)
    return perms


def _matching_adj(N, perms):
    adj = [[] for _ in range(2 * N)]
    for p in perms:
        for a in range(N):
            b = N + p[a]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _matching_sa(d, D, N, rng, deadline):
    if N < d:
        return None
    perms = _init_perms(N, d, rng)
    if perms is None:
        return None
    cost = _bad(2 * N, _matching_adj(N, perms), D)
    T0, T1 = 10.0, 0.3
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)
        t = rng.randrange(d)
        a1, a2 = rng.sample(range(N), 2)
        p = perms[t]
        clash = False
        for s in range(d):
            if s != t and (perms[s][a1] == p[a2] or perms[s][a2] == p[a1]):
                clash = True
                break
        if clash:
            continue
        p[a1], p[a2] = p[a2], p[a1]
        c2 = _bad(2 * N, _matching_adj(N, perms), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            p[a1], p[a2] = p[a2], p[a1]
    if cost != 0:
        return None
    edges = set()
    for p in perms:
        for a in range(N):
            edges.add((a, N + p[a]))
    return 2 * N, sorted(edges)


def _graph_phase(d, D, rng, deadline, best, consider):
    while time.monotonic() < deadline:
        N = best["n"] // 2 + 1
        run_end = min(deadline, time.monotonic() + 8.0)
        res = _matching_sa(d, D, N, rng, run_end)
        if res is not None:
            consider(*res)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = {"n": 0, "e": []}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = list(e)

    # Safe fallback: K_{d,d} (diameter 2, valid for D >= 2).
    n0, e0 = lib.haar_graph(d, range(d))
    best["n"], best["e"] = n0, list(e0)

    # Optimal for D = 3 when d - 1 is a prime power: return immediately.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best["n"], best["e"]

    budget = max(0.2, 0.8 * time_limit - 0.5)
    deadline = start + budget

    # Group lifts first to secure a strong baseline, then direct graph annealing.
    _group_phase(d, D, rng, start + 0.4 * budget, best, consider)
    _graph_phase(d, D, rng, deadline, best, consider)

    if not lib.is_valid(best["n"], best["e"], d, D):
        n0, e0 = lib.haar_graph(d, range(d))
        return n0, list(e0)
    return best["n"], best["e"]
