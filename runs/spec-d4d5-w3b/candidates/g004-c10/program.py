import math
import random
import time

import lib


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _adjacency(k, G, darts, perms):
    """Adjacency lists of the bi-Cayley lift. A-vertices are 0..kG-1, B-vertices kG..2kG-1."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return N, adj


def _reach_cost(N, adj, D):
    """Number of ordered vertex pairs at distance greater than D (0 means diameter <= D)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        changed = False
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            if x != reach[v]:
                changed = True
            new.append(x)
        reach = new
        if not changed:
            break
    return sum(N - r.bit_count() for r in reach)


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            E.add((min(a, b), max(a, b)))
    return 2 * k * G, sorted(E)


def _sample_group(G, rng):
    """Return (order, mul) for a semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 50))
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and block targets; returns (n, edges) with diameter <= D, or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    N, adj = _adjacency(k, G, darts, perms)
    cost = _reach_cost(N, adj, D)

    T0 = max(1.0, 0.05 * cost)
    T_end = 0.3

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / max(1, iters))

        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            N, adj = _adjacency(k, G, darts, perms)
            c2 = _reach_cost(N, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            N, adj = _adjacency(k, G, darts, perms)
            c2 = _reach_cost(N, adj, D)
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

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D >= 4:
        # Annealed bi-Cayley lifts over semidirect products, aimed just above the best order so far.
        while time.monotonic() < deadline:
            k = rng.choice([1, 2, 2, 3, 4])
            base = (best_n + 2 + 2 * k - 1) // (2 * k)
            G = max(2, base + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=2000)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
