import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold family: bi-Cayley lifts over semidirect products Z_m x| Z_k2 with k
# base vertices per side, searched by simulated annealing on the number of
# (representative, vertex) pairs at distance > D.
#
# Vertices: A_{i,g} = i*G + g,  B_{j,h} = (k+j)*G + h.
# Layer L has a permutation p_L of {0..k-1}; dart (i, p_L[i], s) joins
# A_{i,g} to B_{p_L[i], g*s} for every g.  Every A and B vertex then has
# degree d.  Left multiplication by the group is an automorphism, so BFS from
# the 2k representatives A_{i,e}, B_{j,e} is enough.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    ks = [k2 for k2 in _divisors(G) if G // k2 >= 2]
    rng.shuffle(ks)
    for k2 in ks[:12]:
        m = G // k2
        if k2 == 1:
            order, mul, _ = lib.semidirect_group(m, 1, 1)
            return order, mul
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
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    nbrs = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            nbrs[a].append(b)
            nbrs[b].append(a)
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
                for v in nbrs[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline):
    """Annealing over voltages and per-layer B-assignments; temperature decays with elapsed time."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.3

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = T0 * (T_end / T0) ** frac

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
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
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = (0.8 if D >= 5 else 0.3) * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective-plane baseline (diameter 3, valid for any D >= 3).
    pg = _pg_best(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Bold search: bi-Cayley lifts over semidirect products with growing order.
    target = best_n
    attempt_budget = max(2.0, 0.2 * budget)
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 3, 4])
        G = (target + 2 * k) // (2 * k)  # ensures 2*k*G > target
        G += rng.randrange(0, 3)
        g = None
        for _ in range(30):
            g = _sample_group(G, rng)
            if g is not None:
                break
            G += 1
        if g is None:
            continue
        order, mul = g
        tl = min(deadline, time.monotonic() + attempt_budget)
        res = _anneal(d, D, k, order, mul, rng, tl)
        if res is not None:
            n_c, e_c = res
            consider(n_c, e_c)
            if n_c > target:
                target = n_c + 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
