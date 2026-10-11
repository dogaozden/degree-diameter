import itertools
import math
import random
import time

import numpy as np

import lib


_B8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PEN = 1000
_BIG = 10 ** 15


def _popcount(x):
    """Bit count of each non-negative int64 entry (values below 2**63)."""
    total = np.zeros(x.shape, dtype=np.int64)
    for sh in range(0, 64, 8):
        total += _B8[(x >> sh) & 255]
    return total


# ----------------------------------------------------------------------------
# Exact baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d (small q only)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables for Z_m x| Z_k2.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


# ----------------------------------------------------------------------------
# NEW: block-dart lifts with orbit extension.
#
# A "dart" (i, j, s) joins A-block i to B-block j with voltage s:
#     A_{i,g} ~ B_{j, g*s}   for all g in G.
# Left multiplication by any h in G is an automorphism, so the diameter is
# certified by reach bitmasks on the 2K block representatives. Each block
# carries exactly d darts, so the lift is d-regular and bipartite.
#
# Orbit extension (new): remove d-1 darts (i_t, j_t, s_t) and add a whole new
# A-block K and B-block K. Each removed dart is replaced by (i_t, K, new s) and
# (K, j_t, new s'), and the new pair is joined by (K, K, new s''). Blocks keep
# degree d, so the order grows by 2G at once and the graph stays a G-lift.
# Voltage annealing then repairs the diameter.
# ----------------------------------------------------------------------------

def _evaluate(darts, K, G, Ts, Invs, d, D):
    """Return (cost, reach): cost = unreached (representative, vertex) pairs + duplicate penalty."""
    N = 2 * K * G
    nbr = np.zeros((d, N), dtype=np.int64)
    ca = [0] * K
    cb = [0] * K
    seen = set()
    dup = 0
    for i, j, s in darts:
        if ca[i] >= d or cb[j] >= d:
            return _BIG, None
        key = (i, j, s)
        if key in seen:
            dup += 1
        else:
            seen.add(key)
        sa, sb = ca[i], cb[j]
        ca[i] += 1
        cb[j] += 1
        nbr[sa, i * G:(i + 1) * G] = (K + j) * G + Ts[s]
        nbr[sb, (K + j) * G:(K + j + 1) * G] = i * G + Invs[s]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * K):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    unreached = 2 * K * N - int(_popcount(reach).sum())
    return unreached + _PEN * dup, reach


def _anneal(darts, K, G, Ts, Invs, d, D, rng, iters, deadline):
    """Simulated annealing over dart voltages and endpoint swaps. Returns (cost, darts)."""
    cost, reach = _evaluate(darts, K, G, Ts, Invs, d, D)
    if reach is None:
        return _BIG, darts
    full = (1 << (2 * K)) - 1
    t0 = max(0.5, 0.02 * cost)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, t0 * (1.0 - t / iters))
        cand = list(darts)
        if rng.random() < 0.15 and len(cand) >= 2:
            t1, t2 = rng.sample(range(len(cand)), 2)
            i1, j1, s1 = cand[t1]
            i2, j2, s2 = cand[t2]
            cand[t1] = (i1, j2, s1)
            cand[t2] = (i2, j1, s2)
        else:
            bad = np.flatnonzero(reach != full) if rng.random() < 0.5 else None
            idx = None
            if bad is not None and bad.size:
                u = int(bad[rng.randrange(bad.size)])
                b = u // G
                if b < K:
                    pool = [x for x, (i, j, s) in enumerate(cand) if i == b]
                else:
                    pool = [x for x, (i, j, s) in enumerate(cand) if j == b - K]
                if pool:
                    idx = rng.choice(pool)
            if idx is None:
                idx = rng.randrange(len(cand))
            i, j, s = cand[idx]
            ns = rng.randrange(G)
            if ns == s:
                continue
            cand[idx] = (i, j, ns)
        c2, r2 = _evaluate(cand, K, G, Ts, Invs, d, D)
        if r2 is None:
            continue
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            darts, cost, reach = cand, c2, r2
    return cost, darts


def _initial_darts(K, d, G, rng):
    """d random permutation layers over K blocks, with random voltages."""
    darts = []
    for _ in range(d):
        perm = list(range(K))
        rng.shuffle(perm)
        for i in range(K):
            darts.append((i, perm[i], rng.randrange(G)))
    return darts


def _extend(darts, K, G, d, rng):
    """Orbit extension: add one A-block and one B-block of size G, return (darts, K+1)."""
    removed = set(rng.sample(range(len(darts)), d - 1))
    new = [darts[t] for t in range(len(darts)) if t not in removed]
    for t in removed:
        i, j, _ = darts[t]
        new.append((i, K, rng.randrange(G)))
        new.append((K, j, rng.randrange(G)))
    new.append((K, K, rng.randrange(G)))
    return new, K + 1


def _to_edges(darts, K, G, Ts):
    """Expand darts into the explicit lift: (n, edges)."""
    edges = []
    for i, j, s in darts:
        ts = Ts[s].tolist()
        base_a = i * G
        base_b = (K + j) * G
        for g in range(G):
            edges.append((base_a + g, base_b + ts[g]))
    return 2 * K * G, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, max(0.5 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Lift search with orbit extension.
    kmax = 28
    while time.monotonic() < deadline:
        target = rng.randint(50, 160)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        K = rng.choice([2, 3])
        darts = _initial_darts(K, d, G, rng)
        cost, darts = _anneal(darts, K, G, Ts, Invs, d, D, rng, 3000, deadline)
        if cost != 0:
            continue
        n_cur, e_cur = _to_edges(darts, K, G, Ts)
        consider(n_cur, e_cur)

        fails = 0
        while time.monotonic() < deadline and fails < 3 and K < kmax:
            nd, K1 = _extend(darts, K, G, d, rng)
            c, nd2 = _anneal(nd, K1, G, Ts, Invs, d, D, rng, 1500, deadline)
            if c == 0:
                darts, K = nd2, K1
                fails = 0
                n_cur, e_cur = _to_edges(darts, K, G, Ts)
                consider(n_cur, e_cur)
            else:
                fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
