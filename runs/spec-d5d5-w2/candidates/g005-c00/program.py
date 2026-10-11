import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Multi-base cyclic voltage lifts (bi-Cayley style), searched by simulated
# annealing. Each base vertex A_i or B_j lifts to Z_G. A dart (i, j, s) joins
# A_(i,g) to B_(j, g+s) for all g. Every base vertex has degree d, so the
# lift is d-regular and bipartite. Diameter is checked by bitmask BFS from the
# 2k base representatives, using cyclic shifts as the neighbour operator.
# ----------------------------------------------------------------------------


def _rot(x, s, G, mask):
    """Cyclic shift of the bitmask x (bits indexed by Z_G): bit g moves to bit (g+s) mod G."""
    if s == 0:
        return x
    return ((x << s) | (x >> (G - s))) & mask


def _unreached(k, G, D, tup, mask):
    """Total count of (source, vertex) pairs not within distance D, over the 2k base sources.

    Z_G translation is an automorphism, so the sources (A_i, 0) and (B_j, 0) suffice.
    """
    N = 2 * k * G
    total = 0
    for side in (0, 1):
        for src in range(k):
            FA = [0] * k
            FB = [0] * k
            if side == 0:
                FA[src] = 1
            else:
                FB[src] = 1
            VA = FA[:]
            VB = FB[:]
            cnt = 1
            for _ in range(D):
                NB = [0] * k
                NA = [0] * k
                for i, j, s, ns in tup:
                    x = FA[i]
                    if x:
                        NB[j] |= _rot(x, s, G, mask)
                    y = FB[j]
                    if y:
                        NA[i] |= _rot(y, ns, G, mask)
                FA = [0] * k
                FB = [0] * k
                grew = False
                for i in range(k):
                    f = NA[i] & ~VA[i]
                    if f:
                        FA[i] = f
                        VA[i] |= f
                        cnt += f.bit_count()
                        grew = True
                for j in range(k):
                    f = NB[j] & ~VB[j]
                    if f:
                        FB[j] = f
                        VB[j] |= f
                        cnt += f.bit_count()
                        grew = True
                if not grew:
                    break
            total += N - cnt
    return total


def _cost(k, G, D, darts, mask):
    """Zero iff the lift is simple and has diameter <= D. Duplicate darts are penalised heavily."""
    N = 2 * k * G
    tup = [(i, j, s, (G - s) % G) for i, j, s in darts]
    dups = len(tup) - len({(i, j, s) for i, j, s, _ in tup})
    return dups * 4 * N + _unreached(k, G, D, tup, mask)


def _to_graph(k, G, darts):
    """Expand the voltage description into (n, edges). A-vertices are 0..kG-1, B-vertices kG..2kG-1."""
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + (g + s) % G))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, rng, deadline, iters):
    """Anneal voltages and per-layer target permutations until the lift has diameter <= D."""
    mask = (1 << G) - 1
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    N = 2 * k * G
    cost = _cost(k, G, D, darts, mask)
    T0 = 2.0 + 0.02 * N
    T1 = 0.3
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if k == 1 or rng.random() < 0.6:
            # Change one voltage.
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, mask)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            # Swap two target assignments within one layer (keeps each layer a permutation).
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia = L * k + a
            ib = L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, mask)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _to_graph(k, G, darts)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, which has diameter 2 and so is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # D = 3: incidence graph of PG(2, q) for the largest prime power q <= d - 1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break

    # Main search: repeatedly aim for a lift strictly larger than the current best.
    rng = random.Random(seed * 2654435761 + 97 * d + D)
    ks = (1, 2, 3, 4)
    attempt_cap = max(1.5, 0.2 * budget)
    while time.monotonic() < deadline and best[0] < moore:
        k = rng.choice(ks)
        G = best[0] // (2 * k) + 1 + rng.randrange(3)
        if 2 * k * G > moore:
            if 2 * (best[0] // 2 + 1) > moore:
                break
            k, G = 1, best[0] // 2 + 1
        cap = min(deadline, time.monotonic() + attempt_cap)
        res = _anneal(d, D, k, G, rng, cap, 4000)
        if res is not None:
            n, e = res
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
