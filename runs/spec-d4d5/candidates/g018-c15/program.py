import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Groups of a given order: cyclic, direct products Z_a x Z_b, semidirect
# products Z_m x| Z_k2, and AGL(1, p) when G = p(p-1).
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _cyc_mul(m):
    return lambda x, y: (x + y) % m


def _dp_mul(a, b):
    """Direct product Z_a x Z_b, element (x1, x2) coded as x1*b + x2."""
    def mul(x, y):
        x1, x2 = divmod(x, b)
        y1, y2 = divmod(y, b)
        return ((x1 + y1) % a) * b + (x2 + y2) % b
    return mul


def _agl_mul(q):
    """AGL(1, q) = {x -> a x + b}, element (a, b) with a in 1..q-1 coded as (a-1)*q + b."""
    def mul(x, y):
        a, b = divmod(x, q)
        c, e = divmod(y, q)
        a += 1
        c += 1
        return ((a * c) % q - 1) * q + (a * e + b) % q
    return mul


def _group_options(G, rng):
    """Multiplication functions for several (possibly non-abelian) groups of order G."""
    opts = [_cyc_mul(G)]
    for p in range(3, G + 2):
        if p * (p - 1) == G and _is_prime(p):
            opts.append(_agl_mul(p))
            break
    for a in range(2, G):
        if G % a == 0 and a <= G // a:
            opts.append(_dp_mul(a, G // a))
    for k2 in range(2, 13):
        if G % k2 or G // k2 < 3:
            continue
        m = G // k2
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(3, len(rs))):
            _, mul, _ = lib.semidirect_group(m, k2, r)
            opts.append(mul)
    return opts


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts. Base has k vertices per side and d darts. Dart t
# links A_i to B_{tgt[t][i]} with voltage vol[t][i]. Each layer of the lift
# has G vertices; A_{i,g} -- B_{j, g*s}. Left multiplication is an
# automorphism, so distances from one representative per layer suffice.
# ----------------------------------------------------------------------------

def _cost(k, G, d, D, mt, tgt, vol):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    N = 2 * k * G
    keys = set()
    adj = [[] for _ in range(N)]
    for t in range(d):
        tt = tgt[t]
        vt = vol[t]
        for i in range(k):
            j = tt[i]
            s = vt[i]
            key = (i, j, s)
            if key in keys:
                return _BIG
            keys.add(key)
            ba = i * G
            bb = (k + j) * G
            for g in range(G):
                a = ba + g
                b = bb + mt[g][s]
                adj[a].append(b)
                adj[b].append(a)
    total = 0
    sources = list(range(0, k * G, G)) + list(range(k * G, N, G))
    for src in sources:
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


def _anneal(d, D, k, G, mt, rng, deadline, iters):
    """Simulated annealing over voltages and per-dart target permutations."""
    tgt = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        tgt.append(p)
    vol = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cost = _cost(k, G, d, D, mt, tgt, vol)
    T0, T1 = 3.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        t = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = vol[t][i]
            new = rng.randrange(G)
            if new == old:
                continue
            vol[t][i] = new
            c2 = _cost(k, G, d, D, mt, tgt, vol)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                vol[t][i] = old
        else:
            i, i2 = rng.sample(range(k), 2)
            tgt[t][i], tgt[t][i2] = tgt[t][i2], tgt[t][i]
            c2 = _cost(k, G, d, D, mt, tgt, vol)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                tgt[t][i], tgt[t][i2] = tgt[t][i2], tgt[t][i]
    if cost == 0:
        return tgt, vol
    return None


def _lift_edges(k, G, d, mt, tgt, vol):
    E = set()
    for t in range(d):
        for i in range(k):
            j = tgt[t][i]
            s = vol[t][i]
            for g in range(G):
                E.add((i * G + g, (k + j) * G + mt[g][s]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence graph when d - 1 is a prime power (diameter 3).
    if D >= 3 and d >= 3:
        q = d - 1
        if q <= 25 and lib.is_prime_power(q):
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)

    # Search for bi-Cayley lifts over assorted groups, aiming just above the current best order.
    moore = lib._moore_bound(d, D)
    ks_all = [1, 1, 2, 2, 3, 4, 6]
    anneal_iters = 1200
    while time.monotonic() < deadline and best_n < moore:
        ks = [k for k in ks_all if 2 * k * (best_n // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        G = best_n // (2 * k) + 1 + rng.randrange(0, 3)
        if 2 * k * G > moore:
            G = best_n // (2 * k) + 1
        if G < 2 or 2 * k * G > moore:
            continue
        opts = _group_options(G, rng)
        if not opts:
            continue
        mul = rng.choice(opts)
        mt = [[mul(g, s) for s in range(G)] for g in range(G)]
        res = _anneal(d, D, k, G, mt, rng, deadline, anneal_iters)
        if res is not None:
            tgt, vol = res
            n, e = _lift_edges(k, G, d, mt, tgt, vol)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
