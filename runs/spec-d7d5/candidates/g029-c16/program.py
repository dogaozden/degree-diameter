import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or near-exact families (kept as safe baselines).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite voltage lifts over small groups, found by annealing.
#
# Base: b A-blocks and b B-blocks. Each of the d layers l is a permutation
# perm[l] matching A-block i to B-block perm[l][i], with a voltage S[l][i] in G.
# Edges: A_{i,g} ~ B_{perm[l][i], g*s}. Every block vertex then has degree d.
# Group G is Z_m x|_r Z_k2 (r = 1 gives the direct product). Left
# multiplication is an automorphism, so distance checks only need the 2b
# representative vertices (block starts at identity).
#
# This family is distinct from the earlier bi-Cayley search in two ways:
# the base size b is chosen from 1..6 by a bandit, and the group is drawn
# from direct and semidirect products of random orders instead of a fixed
# set of k2 values.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        if k2 == 2 and rng.random() < 0.2:
            r = m - 1
            if math.gcd(r, m) == 1 and pow(r, 2, m) == 1 % m:
                return m, 2, r
            continue
        if rng.random() < 0.3:
            return m, k2, 1  # direct product
        r = None
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
        if r is None:
            continue
        return m, k2, r
    return None


def _group_tables(m, k2, r):
    """Return (G, M, inv): M[g, s] = g*s and inv[s] = s^{-1}; identity is element 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, M, inv


def _set_dart(nbr, b, G, M, inv, l, i, j, s):
    """Write layer l's neighbours for A-block i (matched to B-block j with voltage s), both sides."""
    nbr[l, i * G:(i + 1) * G] = (b + j) * G + M[:, s]
    nbr[l, (b + j) * G:(b + j + 1) * G] = i * G + M[:, inv[s]]


def _reach(b, G, D, nbr, d):
    """Bitmask per vertex: bit t set when representative block t is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for blk in range(2 * b):
        reach[blk * G] = 1 << blk
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _search(d, D, b, G, M, inv, rng, deadline, max_iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * b * G
    full = (1 << (2 * b)) - 1
    perm = [rng.sample(range(b), b) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(b)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(b):
            _set_dart(nbr, b, G, M, inv, l, i, perm[l][i], S[l][i])

    def dups():
        seen = set()
        c = 0
        for l in range(d):
            for i in range(b):
                key = (i, perm[l][i], S[l][i])
                if key in seen:
                    c += 1
                else:
                    seen.add(key)
        return c

    def score():
        reach = _reach(b, G, D, nbr, d)
        miss = int(_POP[full ^ reach].sum())
        return miss + _PENALTY * dups(), reach

    cost, reach = score()
    c0 = float(max(cost, 1))
    best_cost = cost
    last = 0

    for t in range(max_iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / max_iters))

        if b >= 2 and rng.random() < 0.2:
            # Swap the B-targets of two A-blocks within one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            p = perm[l]
            p[i1], p[i2] = p[i2], p[i1]
            _set_dart(nbr, b, G, M, inv, l, i1, p[i1], S[l][i1])
            _set_dart(nbr, b, G, M, inv, l, i2, p[i2], S[l][i2])
            c2, r2 = score()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last = cost, t
            else:
                p[i1], p[i2] = p[i2], p[i1]
                _set_dart(nbr, b, G, M, inv, l, i1, p[i1], S[l][i1])
                _set_dart(nbr, b, G, M, inv, l, i2, p[i2], S[l][i2])
            continue

        # Voltage move, targeted at a defective vertex half the time.
        bad = np.flatnonzero(reach != full) if rng.random() < 0.5 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            blk = u // G
            l = rng.randrange(d)
            if blk < b:
                i = blk
            else:
                i = perm[l].index(blk - b)
        else:
            l = rng.randrange(d)
            i = rng.randrange(b)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, b, G, M, inv, l, i, perm[l][i], new)
        c2, r2 = score()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, b, G, M, inv, l, i, perm[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for l in range(d):
        for u in range(N):
            v = int(nbr[l, u])
            edges.add((u, v) if u < v else (v, u))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)
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

    moore = lib._moore_bound(d, D)

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= moore:
        return best

    # Voltage-lift search with a bandit over base size b.
    Bs = [1, 2, 3, 4, 5, 6]
    trials = {x: 0 for x in Bs}
    wins = {x: 0 for x in Bs}

    def pick_b():
        if rng.random() < 0.25:
            return rng.choice(Bs)
        return max(Bs, key=lambda x: (wins[x] + 1) / (trials[x] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline and best_n < moore:
        b = pick_b()
        G_min = best_n // (2 * b) + 1
        target = G_min + rng.randrange(0, G_min // 10 + 2)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, M, inv = _group_tables(m, k2, r)
        if 2 * b * G <= best_n:
            continue
        trials[b] += 1
        before = best_n
        res = _search(d, D, b, G, M, inv, rng, deadline, 20000, 2000)
        if res is not None:
            consider(res[0], res[1])
            if best_n > before:
                wins[b] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
