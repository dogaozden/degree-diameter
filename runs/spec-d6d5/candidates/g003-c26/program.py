import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families (exact or known-good for small cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New helper 1: vectorised multiplication tables for Z_m x| Z_k2.
#
# MT[s, x] = index of x * s and IT[s, y] = x with x * s = y. Built with numpy
# broadcasting in O(G^2) array work, so no Python-level loop over group pairs.
# ----------------------------------------------------------------------------

def _group_tables(m, k2, r):
    G = m * k2
    X = np.arange(G, dtype=np.int64)
    A = X // k2
    B = X % k2
    pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    # (a, b) * (c, d) = (a + r^b c, b + d), with x = (a, b) and s = (c, d).
    newA = (A[None, :] + pw[B][None, :] * A[:, None]) % m
    newB = (B[None, :] + B[:, None]) % k2
    MT = newA * k2 + newB
    IT = np.argsort(MT, axis=1)  # each row is a permutation, so argsort gives its inverse
    return G, MT, IT


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 = G for Z_m x| Z_k2, preferring non-cyclic groups."""
    divs = [k2 for k2 in range(1, G + 1) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    noncyc = [k2 for k2 in divs if k2 > 1]
    for _ in range(40):
        if noncyc and rng.random() < 0.8:
            k2 = rng.choice(noncyc)
        else:
            k2 = 1
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        pool = {1, m - 1}
        pool.update(rng.sample(range(1, m), min(m - 1, 80)))
        cands = [r for r in pool if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


# ----------------------------------------------------------------------------
# New helper 2: array-based neighbour table and vectorised cost.
#
# Every vertex has exactly d neighbours, one per layer l. nbT[l, v] is the
# neighbour of v in layer l. Updating one voltage rewrites two contiguous
# slices. The cost counts (representative, vertex) pairs not reached within D,
# using numpy frontier expansion.
# ----------------------------------------------------------------------------

def _write_dart(nbT, l, i, j, s, G, k, MT, IT):
    """Write dart (layer l, source i, target j, voltage s) into both sides of nbT."""
    nbT[l, i * G:(i + 1) * G] = (k + j) * G + MT[s]
    nbT[l, (k + j) * G:(k + j + 1) * G] = i * G + IT[s]


def _cost(nbT, reps, N, D):
    """Number of (representative, vertex) pairs not reached within distance D."""
    total = 0
    for src in reps:
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        frontier = np.array([src], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            cand = nbT[:, frontier].ravel()
            new = np.zeros(N, dtype=bool)
            new[cand] = True
            new &= ~vis
            frontier = np.flatnonzero(new)
            if frontier.size == 0:
                break
            vis |= new
            cnt += frontier.size
        total += N - cnt
    return int(total)


# ----------------------------------------------------------------------------
# Annealing over voltages of a d-regular bi-Cayley lift.
#
# Left multiplication by group elements is an automorphism, so the diameter
# is at most D iff the 2k representatives (identity of each A_i and B_j) reach
# all vertices within D.
# ----------------------------------------------------------------------------

def _anneal(d, D, k, G, MT, IT, rng, iters, deadline):
    N = 2 * k * G
    # Layer l pairs source i with target perms[l][i]; each side then gets d darts.
    perms = [rng.sample(range(k), k) for _ in range(d)]
    keys = set()
    S = [[0] * k for _ in range(d)]
    for l in range(d):
        for i in range(k):
            j = perms[l][i]
            for _ in range(60):
                s = rng.randrange(G)
                if (i, j, s) not in keys:
                    break
            else:
                return None
            keys.add((i, j, s))
            S[l][i] = s

    nbT = np.zeros((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _write_dart(nbT, l, i, perms[l][i], S[l][i], G, k, MT, IT)

    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    cur = _cost(nbT, reps, N, D)
    best = cur
    best_S = [row[:] for row in S]

    T0 = 2.0
    for t in range(iters):
        if best == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        l = rng.randrange(d)
        i = rng.randrange(k)
        j = perms[l][i]
        old = S[l][i]
        new = rng.randrange(G)
        if new == old or (i, j, new) in keys:
            continue
        _write_dart(nbT, l, i, j, new, G, k, MT, IT)
        c2 = _cost(nbT, reps, N, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            keys.discard((i, j, old))
            keys.add((i, j, new))
            S[l][i] = new
            cur = c2
            if cur < best:
                best = cur
                best_S = [row[:] for row in S]
        else:
            _write_dart(nbT, l, i, j, old, G, k, MT, IT)

    if best != 0:
        return None
    E = set()
    for l in range(d):
        for i in range(k):
            j = perms[l][i]
            col = MT[best_S[l][i]]
            for x in range(G):
                E.add((i * G + x, (k + j) * G + int(col[x])))
    return N, sorted(E)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D, and optimal for d = 2.
        n = 2 * D
        return n, [(v, (v + 1) % n) for v in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    mb = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Stop early when the Moore bound is met (for example the Fano-type case).
    if best_n >= mb:
        return best

    # Main search: annealed bi-Cayley lifts over semidirect groups.
    # Group orders are sampled just above the current best, so each success
    # raises the target.
    iters = 3000
    while time.monotonic() < deadline and best_n < mb:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        spread = max(3, base // 12)
        G = max(2, base + 1 + rng.randrange(spread))
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            G, MT, IT = _group_tables(m, k2, r)
            res = _anneal(d, D, k, G, MT, IT, rng, iters, deadline)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
