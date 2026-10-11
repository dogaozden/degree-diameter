import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d. It is valid for D >= 3 and gives the calibration record.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts with simulated annealing.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for all g in the group.
# Left multiplication is an automorphism, so each class is one orbit and
# diameter <= D holds iff a BFS of depth D from each of the 2k representatives
# reaches everything.
#
# New in this version: besides semidirect products Z_m x| Z_k, the group
# sampler also draws NON-CYCLIC abelian groups Z_m1 x Z_m2 with explicit
# divisor pairs. Their lifts are a different family from the cyclic and
# semidirect ones the earlier search explored.
# ----------------------------------------------------------------------------

def _abelian_group(m1, m2):
    """Return (order, mul) for Z_m1 x Z_m2, element (a, b) coded as a*m2 + b."""
    def mul(x, y):
        a1, b1 = divmod(x, m2)
        a2, b2 = divmod(y, m2)
        return ((a1 + a2) % m1) * m2 + (b1 + b2) % m2
    return m1 * m2, mul


def _sample_group(G, rng):
    """Return (order, mul) for a random group of order G (abelian or semidirect), or None."""
    if rng.random() < 0.5:
        divs = [m1 for m1 in range(2, G // 2 + 1) if G % m1 == 0 and G // m1 >= 2]
        if divs:
            m1 = rng.choice(divs)
            order, mul = _abelian_group(m1, G // m1)
            return order, mul
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


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return 10 ** 9
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages. Each A_i and B_j has degree d.

    Each of the d layers is a perfect matching between the A and B base vertices
    (a permutation), and each dart carries one voltage in the group.
    Returns (n, edges) with diameter <= D, or None.
    """
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    best_cost = cost
    best_state = ([list(x) for x in darts], list(perms))

    T0, T_floor = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_floor, T0 * (1.0 - it / iters))
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_state = ([list(x) for x in darts], list(perms))
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        darts, perms = best_state
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Main search: annealed lifts over cyclic, semidirect and abelian groups,
    # with 1-3 base vertices per side. Group orders are targeted just above the
    # current best, so each success pushes the target upward.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 4))
        res = _search(d, D, k, G, rng, 1500, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
