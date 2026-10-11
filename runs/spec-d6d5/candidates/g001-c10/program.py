import math
import random
import time

import lib

BIG = 10 ** 9


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G (k2 = 1 gives the cyclic group)."""
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
    """Right translation g -> g*s as a list."""
    return [mul(g, s) for g in range(G)]


def _lift_adj(k, G, darts, perms):
    """Adjacency of the bi-Cayley lift: A_{i,g} ~ B_{j,g*s} for each dart (i, j, s)."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _), pm in zip(darts, perms):
        ba, bb = i * G, (k + j) * G
        for g in range(G):
            a, b = ba + g, bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return N, adj


def _deficit(N, adj, reps, D):
    """Unreached (representative, vertex) pairs within distance D.

    The lift is invariant under left multiplication by the group, so one BFS per
    base-vertex class (one representative per class) decides the whole diameter.
    """
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    N, adj = _lift_adj(k, G, darts, perms)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    return _deficit(N, adj, reps, D)


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters, init=None):
    """Simulated annealing over dart voltages and per-layer B-assignments.

    If init is given, the search warm-starts from a perturbed copy of that
    configuration (iterated local search), instead of a random start.
    Returns (best_cost, best_darts).
    """
    if init is None:
        darts = []
        for _ in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
    else:
        darts = [list(x) for x in init]
        for _ in range(2):
            darts[rng.randrange(len(darts))][2] = rng.randrange(G)

    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    best_cost = cost
    best = [list(x) for x in darts]
    T = max(1.0, 0.1 * cost) if cost < BIG else 5.0
    T_end = 0.3
    decay = (T_end / T) ** (1.0 / iters) if T > T_end else 1.0

    for _ in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            oldp = perms[idx]
            darts[idx][2] = new
            perms[idx] = _perm(mul, G, new)
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = oldp
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

        if cost < best_cost:
            best_cost = cost
            best = [list(x) for x in darts]

    return best_cost, best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])

    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g

        c, darts = _anneal(d, D, k, order, mul, rng, deadline, 400)
        rounds = 0
        while c > 0 and rounds < 3 and time.monotonic() < deadline:
            c, darts = _anneal(d, D, k, order, mul, rng, deadline, 400, init=darts)
            rounds += 1

        if c == 0:
            perms = [_perm(mul, order, s) for _, _, s in darts]
            n, e = _edges(k, order, darts, perms)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
