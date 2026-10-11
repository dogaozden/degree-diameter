import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction family used for D >= 4 (and as a search for D = 3 when the
# projective-plane bound is not reached):
#
#   A graph on 2*k*G vertices, A-side (i, g) and B-side (j, h), with G a
#   finite group (semidirect product Z_m x|_r Z_k) and k base vertices per side.
#   The graph is a union of d "layers". Layer L is a perfect matching of base
#   vertices i -> p_L(i) with a voltage s_{L,i}, giving the edges
#       (i, g) -- (p_L(i), g * s_{L,i})   for all g in G.
#   Every vertex then has degree exactly d and the graph is bipartite.
#
# Unlike a pure bi-Cayley search, the base graph has up to 4 vertices per
# side, the layers are free permutations, and the diameter cost is evaluated
# exactly with bit-parallel ball growth. A simulated annealing search over
# voltages and layer permutations looks for zero unreached vertex pairs.
#
# Nothing here is guaranteed to beat the record. Every returned graph is
# checked with lib.is_valid, and a K_{d,d} fallback is always available.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_CACHE = {}


def _groups(G):
    """Semidirect parameters (m, k, r) with m * k = G, for Z_m x|_r Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r):
    """Cached (order, R) where R[s][g] = g * s in the group."""
    key = (m, k, r)
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    R = [[mul(g, s) for g in range(order)] for s in range(order)]
    if len(_CACHE) > 64:
        _CACHE.clear()
    _CACHE[key] = (order, R)
    return order, R


def _cost(k, G, D, R, perms, volts):
    """Number of ordered vertex pairs not within distance D. Zero means valid.

    Returns _BIG if two darts coincide (that would create a duplicate edge).
    """
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen = set()
    for L, p in enumerate(perms):
        vl = volts[L]
        for i in range(k):
            j = p[i]
            s = vl[i]
            key = (i, j, s)
            if key in seen:
                return _BIG
            seen.add(key)
            ai = i * G
            bj = (k + j) * G
            row = R[s]
            for g in range(G):
                a = ai + g
                b = bj + row[g]
                adj[a].append(b)
                adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    total = 0
    for x in reach:
        total += N - x.bit_count()
    return total


def _edges(k, G, R, perms, volts):
    E = set()
    for L, p in enumerate(perms):
        for i in range(k):
            j = p[i]
            row = R[volts[L][i]]
            for g in range(G):
                E.add((i * G + g, (k + j) * G + row[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, R, rng, stop):
    """Simulated annealing over layer permutations and voltages until stop time."""
    t0 = time.monotonic()
    span = max(1e-3, stop - t0)

    # Random start with no duplicate darts.
    for _ in range(200):
        perms = []
        volts = []
        for _L in range(d):
            p = list(range(k))
            rng.shuffle(p)
            perms.append(p)
            volts.append([rng.randrange(G) for _ in range(k)])
        cost = _cost(k, G, D, R, perms, volts)
        if cost < _BIG:
            break
    else:
        return None

    T0 = max(1.0, 0.03 * cost)
    frac = 0.0
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= stop:
                break
            frac = (now - t0) / span
            T = max(1e-3, T0 * (0.02 ** frac))

        L = rng.randrange(d)
        if k > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(k), 2)
            p = perms[L]
            p[a], p[b] = p[b], p[a]
            c2 = _cost(k, G, D, R, perms, volts)
            if c2 < _BIG and (c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T)):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]
        else:
            i = rng.randrange(k)
            old = volts[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volts[L][i] = new
            c2 = _cost(k, G, D, R, perms, volts)
            if c2 < _BIG and (c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T)):
                cost = c2
            else:
                volts[L][i] = old

    if cost == 0:
        return _edges(k, G, R, perms, volts)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= moore:
        return best

    # D = 3: the projective plane incidence graph attains the Moore bound when d-1 is a prime power.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n2, e2 = lib.projective_plane_incidence(q)
                consider(n2, e2)
                break

    # Main search over layered group lifts with k base vertices per side.
    while time.monotonic() < deadline and best[0] < moore:
        n_best = best[0]
        feasible = [k for k in (1, 1, 2, 2, 3, 4)
                    if n_best // (2 * k) + 1 <= moore // (2 * k)]
        if not feasible:
            break
        k = rng.choice(feasible)
        lo = n_best // (2 * k) + 1
        hi_G = moore // (2 * k)
        hi = min(lo + 6, hi_G + 1)
        cands = list(range(lo, hi))
        if not cands:
            continue
        weights = [max(1, len(_groups(G))) for G in cands]
        G = rng.choices(cands, weights=weights, k=1)[0]

        groups = _groups(G)
        rng.shuffle(groups)
        for m, kk, r in groups[:4]:
            if time.monotonic() >= deadline:
                break
            order, R = _group_tables(m, kk, r)
            stop = min(deadline, time.monotonic() + 6.0)
            res = _anneal(d, D, k, order, R, rng, stop)
            if res is not None:
                consider(res[0], res[1])
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
