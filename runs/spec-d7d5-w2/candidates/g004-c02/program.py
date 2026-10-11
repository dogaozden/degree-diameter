import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New construction for (d, D) = (7, 5): unstructured random bipartite lifts.
#
# A bipartite graph with n = 2N vertices and degree d is given by d permutations
# sig[l] of range(N): A-vertex a is joined to B-vertex sig[l][a] for every layer l.
# Local search (simulated annealing) swaps targets inside one layer and minimises
#   cost = (ordered vertex pairs at distance > D) + PEN * (repeated edges).
# Reachability is tracked with packed uint64 bitsets in numpy, so one evaluation
# is a handful of vectorised gathers. The graph size N is searched by bisection,
# and every accepted graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

_PEN = 8
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _eval_lift(sig, D):
    """Return (bad_pairs, duplicate_count, per-row popcount) for the lift given by sig (d x N)."""
    d, N = sig.shape
    N2 = 2 * N
    inv = np.argsort(sig, axis=1)
    nbr = np.empty((d, N2), dtype=np.int64)
    nbr[:, :N] = N + sig
    nbr[:, N:] = inv
    W = (N2 + 63) // 64
    reach = np.zeros((N2, W), dtype=np.uint64)
    idx = np.arange(N2)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        reach = new
    pop = _POP8[reach.view(np.uint8).reshape(N2, W * 8)].sum(axis=1)
    bad = N2 * N2 - int(pop.sum())
    S = np.sort(sig, axis=0)
    dups = int(np.sum(S[1:] == S[:-1]))
    return bad, dups, pop


def _anneal_lift(d, D, N, rng, nrng, deadline):
    """Anneal a random d-regular bipartite lift on N+N vertices. Returns (sig, cost)."""
    N2 = 2 * N
    sig = np.array([nrng.permutation(N) for _ in range(d)], dtype=np.int64)
    bad, dups, pop = _eval_lift(sig, D)
    cost = bad + _PEN * dups
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(2.0, 0.02 * cost)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        temp = max(0.5, T0 * (1.0 - frac))
        l = rng.randrange(d)
        a1 = None
        if rng.random() < 0.5:
            bad_rows = np.flatnonzero(pop < N2)
            if bad_rows.size:
                v = int(bad_rows[rng.randrange(bad_rows.size)])
                if v < N:
                    a1 = v
                else:
                    hits = np.flatnonzero(sig[l] == v - N)
                    a1 = int(hits[0]) if hits.size else None
        if a1 is None:
            a1 = rng.randrange(N)
        a2 = rng.randrange(N)
        if a1 == a2:
            continue
        sig[l, a1], sig[l, a2] = sig[l, a2], sig[l, a1]
        b2, d2, p2 = _eval_lift(sig, D)
        c2 = b2 + _PEN * d2
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, pop = c2, p2
        else:
            sig[l, a1], sig[l, a2] = sig[l, a2], sig[l, a1]
    return sig, cost


def _lift_edges(sig):
    d, N = sig.shape
    edges = set()
    for l in range(d):
        for a in range(N):
            edges.add((a, N + int(sig[l, a])))
    return 2 * N, sorted(edges)


def _random_lift_search(d, D, seed, deadline):
    """Bisection over N (per-side size) with annealing; returns the largest valid (n, edges) found."""
    rng = random.Random(seed)
    nrng = np.random.default_rng(seed)
    best = None
    good = 0
    fail = None
    N = 300
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0 or N < 20:
            break
        chunk = min(remaining, max(3.0, 0.4 * remaining))
        sig, cost = _anneal_lift(d, D, N, rng, nrng, now + chunk)
        ok = False
        if cost == 0:
            n, edges = _lift_edges(sig)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                good = N
                ok = True
        if ok:
            if fail is None:
                N = int(N * 1.15) + 1
            else:
                if fail - good <= 2:
                    break
                N = (good + fail) // 2
        else:
            if fail is None or N < fail:
                fail = N
            if good == 0:
                N = int(N * 0.8)
            else:
                if fail - good <= 2:
                    break
                N = (good + fail) // 2
    return best


# ----------------------------------------------------------------------------
# Parent baseline families (used for all other cases and as fallback).
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


_KS = (1, 2, 3, 4)
_PENALTY = 1000
_NEAR_MISS = 40
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _sample_group(target, rng):
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
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


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach_bi(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search_bi(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach_bi(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()
        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach_bi(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach_bi(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None, cost
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return (N, sorted(edges)), 0


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res, cost = _search_bi(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is None and cost <= _NEAR_MISS and time.monotonic() < deadline:
            res, cost = _search_bi(d, D, k, G, Ts, Invs, rng, deadline, 12000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    if d == 7 and D == 5:
        budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
        deadline = start + budget
        res = _random_lift_search(d, D, seed, deadline)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
        remaining = time_limit - (time.monotonic() - start)
        if remaining < 6.0:
            return lib.haar_graph(d, range(d))
        return _parent_build(d, D, seed, remaining)

    return _parent_build(d, D, seed, time_limit)
