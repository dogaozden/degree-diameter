"""Bold variant: bi-Cayley lifts over nonabelian groups, with a growing target order.

Family: for a group G (a semidirect product Z_m x| Z_k2 from lib) and k layers per side,
vertices are A_{i,g} and B_{j,h}. Each dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g.
Each layer contributes one dart per A-vertex and one per B-vertex, so the graph is d-regular
and bipartite by construction.

Left multiplication by a group element is an automorphism, so the diameter check only needs
BFS from one representative per (side, layer). Simulated annealing searches over voltages and
the per-layer B-assignments. The target order grows with the best order found so far.
Every candidate is checked with lib.is_valid before it is accepted, and K_{d,d} is the fallback.
"""
import math
import random
import time

import lib

_BIG = 10 ** 9


def _factorizations(G):
    """All (m, k2, r) with m * k2 = G giving a semidirect product Z_m x|_r Z_k2 of order G."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _cost(k, G, D, darts, R):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    keys = set()
    for dart in darts:
        key = (dart[0], dart[1], dart[2])
        if key in keys:
            return _BIG
        keys.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        Rs = R[s]
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + Rs[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _anneal(k, d, D, G, R, rng, deadline, iters):
    """Simulated annealing over voltages and layer assignments. Returns darts with cost 0, or None."""
    if k == 1:
        if G < d:
            return None
        darts = [[0, 0, s] for s in rng.sample(range(G), d)]
    else:
        darts = []
        for _ in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])

    cost = _cost(k, G, D, darts, R)
    T0 = 3.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (0.1 ** (it / iters))
        if k == 1 or rng.random() < 0.75:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            used = {x[2] for x in darts}
            new = rng.randrange(G)
            if new == old or (k == 1 and new in used):
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, R)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, R)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return darts if cost == 0 else None


def _edges(k, G, darts, R):
    """Expand darts into the bipartite graph on 2*k*G vertices."""
    E = set()
    for i, j, s in darts:
        Rs = R[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + Rs[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best
        if res is None:
            return
        n, e = res
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(lib.projective_plane_incidence(q))
                break
        if d >= 3 and lib.is_prime_power(d - 1):
            # PG(2, d-1) is extremal for this case; no search needed.
            return best

    if d >= 2:
        factor_cache = {}
        iters = 2000
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 1, 2])
            G = best[0] // (2 * k) + 1 + rng.randrange(0, 3)
            if G < 2:
                G = 2
            if G not in factor_cache:
                factor_cache[G] = _factorizations(G)
            opts = factor_cache[G]
            if not opts:
                continue
            m, k2, r = rng.choice(opts)
            try:
                order, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            R = [[mul(g, s) for g in range(order)] for s in range(order)]
            darts = _anneal(k, d, D, order, R, rng, deadline, iters)
            if darts is not None:
                consider(_edges(k, order, darts, R))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
