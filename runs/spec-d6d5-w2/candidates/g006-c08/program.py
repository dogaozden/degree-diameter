import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Deterministic families used as the starting point and as fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley lifts over small non-abelian-capable groups
# Z_m x| Z_k2, with k base vertices per side.
#
# Vertices: A_{i,g} = i*G + g,  B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g in the group.
# Each layer L is a permutation p_L of range(k) (A_i -> B_{p_L[i]}), so every
# vertex has degree exactly d. Left translations are automorphisms, so it is
# enough to measure distances from the identity representatives A_{i,e}, B_{j,e}.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    divs = [x for x in range(1, min(G, 12) + 1) if G % x == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            order, mul, _ = lib.semidirect_group(m, 1, 1)
            return order, mul
        for _ in range(60):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                order, mul, _ = lib.semidirect_group(m, k2, r)
                return order, mul
    return None


def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, N):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    keys = {(i, j, s) for i, j, s, _ in darts}
    if len(keys) < len(darts):
        return _BIG
    adj = [[] for _ in range(N)]
    for i, j, _s, pm in darts:
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
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Metropolis search over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    p = [rng.sample(range(k), k) for _ in range(d)]
    darts = []  # each entry: [i, j, s, perm]
    for L in range(d):
        for i in range(k):
            s = rng.randrange(G)
            darts.append([i, p[L][i], s, _perm(mul, G, s)])
    cur = _cost(k, G, D, darts, N)
    T = 1.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cur - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            t = rng.randrange(d * k)
            old_s, old_pm = darts[t][2], darts[t][3]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[t][2] = new_s
            darts[t][3] = _perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, N)
            if c2 <= limit:
                cur = c2
            else:
                darts[t][2], darts[t][3] = old_s, old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ta, tb = L * k + a, L * k + b
            darts[ta][1], darts[tb][1] = darts[tb][1], darts[ta][1]
            c2 = _cost(k, G, D, darts, N)
            if c2 <= limit:
                cur = c2
            else:
                darts[ta][1], darts[tb][1] = darts[tb][1], darts[ta][1]
    if cur != 0:
        return None
    E = set()
    for i, j, _s, pm in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return N, sorted(E)


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: bi-Cayley lifts with annealed voltages over small groups.
    # The group order G is chosen just above what is needed to beat best_n.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2])
        lo = max(2, best_n // (2 * k) + 1)
        G = rng.randint(lo, lo + max(3, lo // 5))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        iters = 1500 if k == 1 else 600
        res = _anneal(d, D, k, order, mul, rng, deadline, iters)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
