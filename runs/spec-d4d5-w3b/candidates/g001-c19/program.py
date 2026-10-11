import math
import random
import time

import lib


BIG = 10 ** 9


def _bad_pairs_bits(N, adj, D):
    """Ordered count of (source, target) pairs at distance > D, using bitmask balls. Zero means diameter <= D."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(N - b.bit_count() for b in ball)


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    opts = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not opts:
        return None
    for _ in range(40):
        k2 = rng.choice(opts)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = []
            for r_try in rng.sample(range(1, m), min(m - 1, 50)):
                if math.gcd(r_try, m) == 1 and pow(r_try, k2, m) == 1 % m:
                    cands.append(r_try)
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _anneal(d, D, k, G, mul, rng, deadline, max_iters):
    """Anneal a d-regular bipartite bi-Cayley lift with k base vertices per side over a group of order G.

    Layer L has a permutation tgt[L] (A_i -> B_{tgt[L][i]}) and voltages volt[L][i].
    Edge A_{i,g} -- B_{j, g*s} for each dart. Returns (n, edges) with diameter <= D, or None.
    """
    P = [[mul(g, s) for g in range(G)] for s in range(G)]
    N = 2 * k * G
    tgt = []
    volt = []
    for _ in range(d):
        tgt.append(rng.sample(range(k), k))
        volt.append([rng.randrange(G) for _ in range(k)])

    def cost():
        keys = set()
        for L in range(d):
            for i in range(k):
                key = (i, tgt[L][i], volt[L][i])
                if key in keys:
                    return BIG
                keys.add(key)
        adj = [[] for _ in range(N)]
        for L in range(d):
            for i in range(k):
                j = tgt[L][i]
                pm = P[volt[L][i]]
                ba = i * G
                bb = (k + j) * G
                for g in range(G):
                    a = ba + g
                    b = bb + pm[g]
                    adj[a].append(b)
                    adj[b].append(a)
        return _bad_pairs_bits(N, adj, D)

    c = cost()
    T0, T1 = 3.0, 0.2
    for it in range(max_iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, max_iters))
        if k == 1 or rng.random() < 0.7:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            c2 = cost()
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                volt[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            tgt[L][a], tgt[L][b] = tgt[L][b], tgt[L][a]
            c2 = cost()
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                c = c2
            else:
                tgt[L][a], tgt[L][b] = tgt[L][b], tgt[L][a]

    if c != 0:
        return None
    edges = set()
    for L in range(d):
        for i in range(k):
            j = tgt[L][i]
            pm = P[volt[L][i]]
            for g in range(G):
                edges.add((i * G + g, (k + j) * G + pm[g]))
    return N, sorted((int(a), int(b)) for a, b in edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    if D >= 3:
        moore = lib.moore_bound(d, D)
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 2, 2, 3, 4])
            G = best_n // (2 * k) + 1 + rng.randrange(0, 3)
            if 2 * k * G > moore:
                G = max(2, moore // (2 * k))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            budget = min(deadline, time.monotonic() + 8.0)
            res = _anneal(d, D, k, order, mul, rng, budget, 4000)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, [(int(u), int(v)) for u, v in best_e]
