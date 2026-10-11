import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks.
# ----------------------------------------------------------------------------

def _k_dd(d):
    """K_{d,d}: degree d, diameter 2, always valid for D >= 2."""
    return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group tables for Z_m x| Z_k (element a*k+b, (a,b)(c,e) = (a + r^b c, b + e)).
# M[x, y] = x*y, inv[x] = x^{-1}, identity = 0.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(M == 0)
    inv[rows] = cols
    return G, M, inv


def _sample_group(target, rng):
    """Return (m, k, r) with m*k >= target and r^k = 1 mod m, gcd(r, m) = 1, or None."""
    for _ in range(300):
        k = rng.choice([1, 2, 2, 3, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 28, 30, 36])
        m = max(2, -(-target // k))
        if k == 1:
            return m, 1, 1
        for _ in range(60):
            r = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return m, k, r
    return None


# ----------------------------------------------------------------------------
# Family A (new, bold): single-orbit Haar graphs over nonabelian groups.
#
# Haar graph H(G, S): vertices a_g, b_g (g in G); a_g ~ b_{g s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the diameter is the max of the
# eccentricities of a_e and b_e. Each candidate S is checked by two cheap BFS
# runs, and S is improved by annealing single-element swaps. No k-layer lift.
# ----------------------------------------------------------------------------

def _haar_cost(G, M, inv, S, D):
    """Total number of (source, vertex) pairs at distance > D from a_e and b_e. Zero iff diameter <= D."""
    nbr = np.empty((2 * G, S.size), dtype=np.int64)
    nbr[:G] = G + M[:, S]
    nbr[G:] = M[:, inv[S]]
    cost = 0
    for src in (0, G):
        seen = np.zeros(2 * G, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            seen[nxt] = True
            frontier = nxt
        cost += 2 * G - int(seen.sum())
    return cost


def _haar_search(G, M, inv, d, D, rng, budget):
    """Anneal a connection set S of size d; return (n, edges) with diameter <= D, or None."""
    lst = rng.sample(range(G), d)
    cost = _haar_cost(G, M, inv, np.array(lst, dtype=np.int64), D)
    best, stale, T = cost, 0, 1.0
    for _ in range(budget):
        if cost == 0:
            break
        pos = rng.randrange(d)
        new = rng.randrange(G)
        if new in lst:
            continue
        cand = lst[:]
        cand[pos] = new
        c = _haar_cost(G, M, inv, np.array(cand, dtype=np.int64), D)
        if c <= cost or rng.random() < math.exp(-(c - cost) / T):
            lst, cost = cand, c
        if cost < best:
            best, stale = cost, 0
        else:
            stale += 1
        if stale > 500:
            lst = rng.sample(range(G), d)
            cost = _haar_cost(G, M, inv, np.array(lst, dtype=np.int64), D)
            best, stale = cost, 0
    if cost != 0:
        return None
    edges = [(g, G + int(M[g, s])) for g in range(G) for s in lst]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Family B (parent's bi-Cayley k-layer lift over Z_m x| Z_k), kept as the
# second stage so the parent's record-level search is still available.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over layer permutations and voltages. Returns (n, edges) or None."""
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

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
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
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _k_dd(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        hard = start + max(1.0, min(time_limit - 8.0, 0.9 * time_limit))
        split = start + 0.4 * (hard - start)

        # Stage A: single-orbit Haar graphs over nonabelian groups.
        while time.monotonic() < split:
            target = best_n // 2 + 1 + rng.randrange(0, 40)
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k, r = g
            G, M, inv = _group_table(m, k, r)
            if 2 * G <= best_n:
                continue
            res = _haar_search(G, M, inv, d, D, rng, 3000)
            if res is not None:
                consider(res[0], res[1])

        # Stage B: bi-Cayley k-layer lifts (parent's record-level search).
        while time.monotonic() < hard:
            k = rng.choice(_KS)
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, M, inv = _group_table(m, k2, r)
            if 2 * k * G <= best_n:
                continue
            Ts = np.ascontiguousarray(M.T)
            Invs = np.ascontiguousarray(M[:, inv].T)
            res = _search(d, D, k, G, Ts, Invs, rng, hard, 4000, 1200)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return _k_dd(d)
    return best
