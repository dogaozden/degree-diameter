import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over groups of order G, searched by iterated local
# search with plateau moves and random perturbation restarts.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Each "layer" L is a bijection p_L from A-blocks to B-blocks, and each dart
# (i, p_L(i), s) joins A_i,g to B_{p_L(i)}, g*s for all g. Every vertex then
# has degree exactly d. The group acts by left multiplication, so distances
# only need to be checked from the 2k block representatives.
# ----------------------------------------------------------------------------

def _perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid.

    Returns early with a value above `limit` once the running total exceeds it.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    """Expand darts into the full edge list of the lift."""
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _ils(d, D, k, G, mul, rng, deadline, max_iters, stall_limit=400):
    """Iterated local search over voltages and layer assignments.

    Moves that do not increase the cost are accepted (plateau walk). After
    `stall_limit` consecutive non-improving moves, a few darts are re-randomized.
    Returns (darts, perms) with zero cost, or None.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    stall = 0

    for _ in range(max_iters):
        if cost == 0:
            return darts, perms
        if time.monotonic() > deadline:
            return None

        if stall >= stall_limit:
            for _ in range(max(2, len(darts) // 4)):
                idx = rng.randrange(len(darts))
                darts[idx][2] = rng.randrange(G)
                perms[idx] = _perm(mul, G, darts[idx][2])
            cost = _cost(k, G, D, darts, perms)
            stall = 0
            continue

        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                stall += 1
                continue
            old_perm = perms[idx]
            darts[idx][2] = new
            perms[idx] = _perm(mul, G, new)
            c2 = _cost(k, G, D, darts, perms, cost)
            if c2 <= cost:
                stall = 0 if c2 < cost else stall + 1
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = old_perm
                stall += 1
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, cost)
            if c2 <= cost:
                stall = 0 if c2 < cost else stall + 1
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                stall += 1

    return (darts, perms) if cost == 0 else None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G as (order, mul), or None."""
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


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 0.5)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Incidence graph of PG(2, d-1) when d-1 is a prime power: diameter 3, optimal.
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    # Main search: annealed-style group voltage lifts with iterated local search.
    ks = [1, 2, 2, 3, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))

        grp = _sample_group(G, rng)
        if grp is None:
            order, mul, _ = lib.cyclic_group(G)
        else:
            order, mul = grp

        res = _ils(d, D, k, order, mul, rng, deadline, max_iters=3000)
        if res is not None:
            darts, perms = res
            n, e = _edges(k, order, darts, perms)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
