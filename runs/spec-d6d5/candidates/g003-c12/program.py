import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for D >= 4: bi-Cayley voltage lifts over small semidirect
# products, searched by simulated annealing. The cost is computed with
# bitset ball propagation over all vertices (no per-source BFS), and the
# search is restarted across many (k, group) pairs until the deadline.
# Diameter-3 bases (projective planes) remain as the safe fallback.
# ----------------------------------------------------------------------------


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
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


def _perm(mul, G, s):
    """Right multiplication g -> g*s as a permutation list."""
    return [mul(g, s) for g in range(G)]


def _adjacency(k, G, darts, perms):
    """Adjacency lists of the bi-Cayley lift (A side 0..kG-1, B side kG..2kG-1)."""
    N = 2 * k * G
    nb = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            nb[a].append(b)
            nb[b].append(a)
    return nb


def _cost(N, nb, D):
    """Total number of ordered vertex pairs at distance > D, via bitset ball propagation."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in nb[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and layer target assignments. Returns (darts, perms) on success, else None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm(mul, G, s) for _, _, s in darts]
    N = 2 * k * G

    def evaluate():
        return _cost(N, _adjacency(k, G, darts, perms), D)

    cost = evaluate()
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm(mul, G, new_s)
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return darts, perms
    return None


def _lift_edges(k, G, darts, perms):
    """Edge list of the lift with vertices 0..2kG-1."""
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Diameter-3 bases: projective plane incidence and the Araujo-Pardo-Lopez extension.
    pg = _pg_best(d)
    if pg is not None:
        consider(pg[0], pg[1])
    if D == 3 and d >= 4 and lib.is_prime_power(d - 2) and d - 2 >= 3 \
            and not lib.is_prime_power(d - 1):
        try:
            n_a, e_a = lib.araujo_lopez_graph(d - 2)
            consider(n_a, e_a)
        except ValueError:
            pass
    if D == 3:
        return best

    # Main search for D >= 4: annealed bi-Cayley lifts over semidirect products.
    ks = [1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = max(2, best_n // (2 * k))
        G = base + 1 + rng.randrange(0, max(3, base // 5))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, 600)
        if res is None:
            continue
        darts, perms = res
        n, e = _lift_edges(k, order, darts, perms)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
