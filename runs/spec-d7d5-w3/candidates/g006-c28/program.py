import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _semidirect_tables(m, k2, r):
    """Tables for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
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


def _group_options(G):
    """All (m, k2, r) with m*k2 = G giving a semidirect product Z_m x| Z_k2 (r = 1 when k2 = 1)."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


# ----------------------------------------------------------------------------
# New construction: single-orbit bi-Cayley graphs.
# Vertices A_g = g and B_g = G + g over a group G of order G. Connection set
# S = {s_0..s_{d-1}} (distinct) gives edges A_g ~ B_{g*s}. Left multiplication
# is an automorphism, so diameter <= D is equivalent to A_e and B_e reaching
# every vertex within D steps. Simulated annealing over S, with a sweep of
# group orders starting just above the record side length.
# ----------------------------------------------------------------------------

def _single_cost(G, nbr, D):
    """Number of unreached (source, vertex) pairs for sources A_e and B_e."""
    reach = np.zeros(2 * G, dtype=np.int64)
    reach[0] = 1
    reach[G] = 2
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 4 * G - int(_POP[reach].sum())


def _single_search(d, D, G, Ts, Invs, rng, deadline, iters, patience):
    """Anneal a distinct connection set S of size d. Returns (n, edges) or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    nbr = np.empty((d, 2 * G), dtype=np.int64)
    for l, s in enumerate(S):
        nbr[l, :G] = G + Ts[s]
        nbr[l, G:] = Invs[s]
    cost = _single_cost(G, nbr, D)
    c0 = float(max(cost, 1))
    best = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.3, 0.03 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        nbr[l, :G] = G + Ts[new]
        nbr[l, G:] = Invs[new]
        c2 = _single_cost(G, nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best:
                best, last = cost, t
        else:
            S[l] = old
            nbr[l, :G] = G + Ts[old]
            nbr[l, G:] = Invs[old]
    if cost != 0:
        return None
    edges = [(g, G + int(Ts[s][g])) for s in S for g in range(G)]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Fallback family: k-block voltage lifts over semidirect products (general search).
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach_multi(k, G, D, nbr, d):
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


def _search_k(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Anneal a k-block voltage lift. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def cost_of():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        dup = len(keys) - len(set(keys))
        reach = _reach_multi(k, G, D, nbr, d)
        return 2 * k * N - int(_POP[reach].sum()) + _PENALTY * dup

    cost = cost_of()
    c0 = float(max(cost, 1))
    best = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        if k >= 2 and rng.random() < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = cost_of()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
                if cost < best:
                    best, last = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = cost_of()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best:
                best, last = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)
    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D <= 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact projective-plane construction (instant for calibration).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (new): single-orbit bi-Cayley search with an adaptive sweep of group orders.
    new_deadline = start + 0.6 * budget
    floor = max(d, 2)
    lo = None
    hi = None
    G = max(floor, best[0] // 2 + 1)
    while time.monotonic() < new_deadline:
        ok = False
        opts = _group_options(G)
        if opts:
            for _ in range(3):
                if time.monotonic() > new_deadline:
                    break
                m, k2, r = rng.choice(opts)
                Gg, Ts, Invs = _semidirect_tables(m, k2, r)
                res = _single_search(d, D, Gg, Ts, Invs, rng, new_deadline, 8000, 2500)
                if res is not None:
                    ok = True
                    consider(res[0], res[1])
                    break
        if ok:
            lo = G if lo is None else max(lo, G)
        else:
            hi = G if hi is None else min(hi, G)
        if lo is not None and hi is not None:
            G = (lo + hi) // 2 if hi - lo > 1 else hi
        elif lo is not None:
            G = lo + max(1, lo // 25)
        else:
            G = max(floor, hi - max(1, hi // 25))
        G = max(floor, G)

    # Phase 2 (fallback): k-block voltage lifts with a bandit over base sizes.
    ks = (2, 3, 4)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}
    deadline = start + budget
    while time.monotonic() < deadline:
        if rng.random() < 0.3:
            k = rng.choice(ks)
        else:
            k = max(ks, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        opts = []
        Gc = target
        while not opts and Gc < target + 50:
            opts = _group_options(Gc)
            if not opts:
                Gc += 1
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        Gg, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * Gg <= best[0]:
            continue
        trials[k] += 1
        res = _search_k(d, D, k, Gg, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
