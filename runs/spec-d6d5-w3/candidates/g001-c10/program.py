import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Cheap baselines: projective plane incidence and Araujo-Pardo-Lopez (D = 3).
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2,
# searched with a fast multi-source bitmask diameter cost.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Left multiplication by the group is an automorphism, so distances from
# each fiber representative (A_i,1 and B_j,1) certify the whole graph.
# Each layer L is a permutation p_L of range(k), so every vertex has degree d.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(100):
        k2 = rng.choice(choices)
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


def _make_perm(G, mul):
    """Cached map s -> list g -> mul(g, s)."""
    cache = {}

    def perm(s):
        pm = cache.get(s)
        if pm is None:
            pm = [mul(g, s) for g in range(G)]
            cache[s] = pm
        return pm

    return perm


def _cost(k, G, D, darts, perm):
    """Number of (representative, vertex) pairs not within distance D. Zero iff valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG  # parallel edges would appear
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = perm(s)
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = [0] * N
    for t, v in enumerate(reps):
        R[v] |= 1 << t
    for _ in range(D):
        newR = R[:]
        for v in range(N):
            x = newR[v]
            for u in adj[v]:
                x |= R[u]
            newR[v] = x
        R = newR
    nr = len(reps)
    return sum(nr - R[v].bit_count() for v in range(N))


def _edges(k, G, darts, perm):
    E = set()
    for i, j, s in darts:
        pm = perm(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, perm, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (ok, darts, cost)."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cost = _cost(k, G, D, darts, perm)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        idx = rng.randrange(len(darts))
        if k == 1 or rng.random() < 0.8:
            old = darts[idx][:]
            darts[idx][2] = rng.randrange(G)
            c2 = _cost(k, G, D, darts, perm)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx] = old
        else:
            L = idx // k
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perm)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost == 0, darts, cost


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _pg_best(d)
            if pg is not None:
                consider(pg[0], pg[1])
            if D == 3:
                ar = _araujo(d)
                if ar is not None:
                    consider(ar[0], ar[1])

        # Calibration cases with a known optimal graph return immediately.
        if best_n >= lib.moore_bound(d, D):
            return best

        # Bi-Cayley lift search, ratcheting upward from the current best order.
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = rng.randint(max(2, base + 1), max(2, base + 1) + max(4, base // 10))
            if G < d:
                continue
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            if order < d:
                continue
            perm = _make_perm(order, mul)
            iters = 3000 if k == 1 else 1500
            ok, darts, _ = _anneal(d, D, k, order, perm, rng, deadline, iters)
            if ok:
                n, e = _edges(k, order, darts, perm)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
