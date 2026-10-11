import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe algebraic fallbacks: K_{d,d}, cycles, PG(2,q) incidence, W(q) incidence.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched with a
# vectorised ball-coverage evaluator.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g.
# Left multiplication is an automorphism, so distances are needed only from
# the 2k base vertices at the identity. The cost is the number of
# (base vertex, vertex) pairs at distance > D; zero means diameter <= D.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    k2s = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not k2s:
        return None
    for _ in range(30):
        k2 = rng.choice(k2s)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _perms(s, G, mul, inv, cache):
    """Forward and backward right-multiplication arrays for generator s (cached)."""
    if s not in cache:
        si = inv(s)
        fwd = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
        bwd = np.fromiter((mul(h, si) for h in range(G)), dtype=np.int64, count=G)
        cache[s] = (fwd, bwd)
    return cache[s]


def _cost(k, G, D, darts, cache, mul, inv):
    """Unreached (base vertex, vertex) pairs within distance D. Zero means diameter <= D."""
    seen = set()
    ops = []
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return _BIG
        seen.add(key)
        fwd, bwd = _perms(s, G, mul, inv, cache)
        ops.append((i, k + j, fwd, bwd))
    R = 2 * k
    reach = np.zeros((R, R, G), dtype=bool)
    ar = np.arange(R)
    reach[ar, ar, 0] = True
    for _ in range(D):
        new = reach.copy()
        for a, b, fwd, bwd in ops:
            new[:, b, fwd] |= reach[:, a, :]
            new[:, a, bwd] |= reach[:, b, :]
        reach = new
    return R * R * G - int(reach.sum())


def _init_darts(d, k, G, rng):
    if k == 1:
        if G < d:
            return None
        return [[0, 0, s] for s in rng.sample(range(G), d)]
    for _ in range(50):
        darts = []
        for _layer in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
        if len({(a, b, c) for a, b, c in darts}) == len(darts):
            return darts
    return None


def _anneal(d, D, k, G, mul, inv, cache, rng, t_end):
    """Time-bounded annealing over generators and layer permutations. Returns darts or None."""
    darts = _init_darts(d, k, G, rng)
    if darts is None:
        return None
    cost = _cost(k, G, D, darts, cache, mul, inv)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - t0) / span
        T = 0.3 + 3.0 * (1.0 - frac)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, cache, mul, inv)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, cache, mul, inv)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return darts
    return None


def _edges(k, G, darts, cache, mul, inv):
    E = set()
    for i, j, s in darts:
        fwd, _ = _perms(s, G, mul, inv, cache)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(fwd[g])))
    return 2 * k * G, sorted(E)


def _attempt(d, D, k, G, rng, t_end):
    g = _sample_group(G, rng)
    if g is None:
        return None
    _, mul, inv = g
    cache = {}
    darts = _anneal(d, D, k, G, mul, inv, cache, rng, t_end)
    if darts is None:
        return None
    return _edges(k, G, darts, cache, mul, inv)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.2, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: bi-Cayley lifts with k base pairs, aiming above the current best.
    while time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        slice_t = min(remaining, max(2.0, min(8.0, 0.15 * remaining)))
        k = 1 if rng.random() < 0.6 else 2
        cur_n = best[0]
        G_min = cur_n // (2 * k) + 1
        G = G_min + (rng.randrange(0, 4) if rng.random() < 0.5 else 0)
        if G < d:
            continue
        res = _attempt(d, D, k, G, rng, time.monotonic() + slice_t)
        if res is not None:
            consider(res[0], res[1])
        if best[0] >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
