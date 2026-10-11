import math
import random
import time

import lib


BIG = 10 ** 9
FRAC_END = 0.82     # fraction of time_limit after which no new search starts
ANNEAL_ITERS = 1500


# ----------------------------------------------------------------------------
# Random group sampling: Z_m x| Z_k2 of total order G (k2 = 1 gives cyclic).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12])
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
# Bit-parallel cost for group lifts.
#
# Vertices: A(i,g) = i*G + g, B(j,h) = (k+j)*G + h.
# Dart (i, j, s) joins A(i,g) to B(j, g*s) for every g. Each layer is a
# permutation p of the k base vertices, giving every vertex degree d.
# Left multiplication is an automorphism, so only one representative per
# (side, base vertex) needs its radius-D ball measured.
# ----------------------------------------------------------------------------

def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
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
    R = [1 << v for v in range(N)]
    for _ in range(D):
        nR = [0] * N
        for v in range(N):
            x = R[v]
            for u in adj[v]:
                x |= R[u]
            nR[v] = x
        R = nR
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        total += N - R[src].bit_count()
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < BIG else 1.0
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
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
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _lift_search(d, D, start_n, moore, deadline, rng):
    """Repeatedly anneal group lifts with order just above the current best.

    Returns the largest valid (n, edges) found, or None.
    """
    best = None
    cur_n = start_n
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 2, 3]
    while time.monotonic() < deadline and cur_n < moore:
        k = rng.choice(ks)
        base = cur_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        try:
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
        except Exception:
            res = None
        if res is not None and res[0] > cur_n and lib.is_valid(res[0], res[1], d, D):
            best = res
            cur_n = res[0]
    return best


# ----------------------------------------------------------------------------
# Algebraic baselines (diameter 3).
# ----------------------------------------------------------------------------

def _pg_incidence(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC_END * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib.moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Algebraic baselines for D = 3.
    if D == 3:
        try:
            consider(_pg_incidence(d))
        except Exception:
            pass
        if best[0] >= moore:
            return best
        try:
            consider(_araujo(d))
        except Exception:
            pass
        return best

    # D >= 4: group-lift search with bit-parallel cost.
    try:
        res = _lift_search(d, D, best[0], moore, deadline, rng)
        consider(res)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
