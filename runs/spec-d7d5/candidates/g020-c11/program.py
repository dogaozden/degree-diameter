import math
import random
import time

import numpy as np

import lib


# Popcount table for bitmasks over at most 8 representative blocks.
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PEN = 20  # penalty per duplicate dart (same block pair and voltage)


# ----------------------------------------------------------------------------
# Safe fallback: incidence graph of PG(2, q) for the largest prime power q <= d-1.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            try:
                return lib.projective_plane_incidence(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------
# Group tables. Every group is given by a multiplication table MUL with the
# identity coded as 0.
# ----------------------------------------------------------------------------

def _group_semidirect(m, k, r):
    """Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e); element coded a*k+b. r^k = 1 mod m."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    MUL = ((a[:, None] + pw[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return G, MUL


def _group_dihedral(m):
    """Dihedral group of order 2m: element (s,t) coded s*m+t acts as z -> (-1)^s z + t."""
    G = 2 * m
    x = np.arange(G, dtype=np.int64)
    s = x // m
    t = x % m
    sign = np.where(s == 0, 1, -1).astype(np.int64)
    MUL = ((s[:, None] + s[None, :]) % 2) * m + (t[:, None] + sign[:, None] * t[None, :]) % m
    return G, MUL


def _inverse(G, MUL):
    INV = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(MUL == 0)
    INV[rows] = cols
    return INV


def _sample_group(lo, rng):
    """Sample a group of order >= lo from cyclic, dihedral, or semidirect families."""
    lo = max(2, lo)
    t = rng.random()
    if t < 0.3:
        m = lo + rng.randrange(0, max(1, lo // 25) + 1)
        return _group_semidirect(m, 1, 1)
    if t < 0.5:
        m = -(-lo // 2) + rng.randrange(0, max(1, lo // 50) + 1)
        return _group_dihedral(max(2, m))
    k2 = rng.choice((2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16))
    m = max(2, -(-lo // k2)) + rng.randrange(0, max(1, lo // (25 * k2)) + 1)
    r = 1
    if rng.random() < 0.6 and m > 2:
        for _ in range(60):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return _group_semidirect(m, k2, r)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a finite group.
#
# Blocks 0..k-1 are A-side, k..2k-1 are B-side, each of size G. Layer l pairs
# A-block i with B-block perm[l][i] and voltage S[l][i]:
#     A(i,x) ~ B(j, x*s).
# Every layer is a bijection, so the graph is d-regular and bipartite.
# Left multiplication by a group element is an automorphism, so the diameter
# condition reduces to: every vertex reaches every block representative
# (block identity) within distance D.
# ----------------------------------------------------------------------------

def _search(d, D, k, G, MUL, INV, rng, deadline, iters, patience):
    """Simulated annealing over perms and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    nb = 2 * k
    perm = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def set_layer(l):
        for i in range(k):
            j = perm[l][i]
            s = S[l][i]
            nbr[l, i * G:(i + 1) * G] = (k + j) * G + MUL[:, s]
            nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + MUL[:, INV[s]]

    for l in range(d):
        set_layer(l)

    def dups():
        keys = [(i, perm[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def evaluate():
        reach = np.zeros(N, dtype=np.int64)
        for b in range(nb):
            reach[b * G] = 1 << b
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        unreached = nb * N - int(_POP8[reach].sum())
        return unreached + _PEN * dups()

    cost = evaluate()
    best_cost = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last > patience:
            break
        T = max(0.25, 2.0 * (1.0 - t / iters))
        l = rng.randrange(d)
        if k >= 2 and rng.random() < 0.2:
            i1, i2 = rng.sample(range(k), 2)
            p = perm[l]
            p[i1], p[i2] = p[i2], p[i1]
            set_layer(l)
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                p[i1], p[i2] = p[i2], p[i1]
                set_layer(l)
                continue
        else:
            i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            set_layer(l)
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                S[l][i] = old
                set_layer(l)
                continue
        if cost < best_cost:
            best_cost = cost
            last = t

    if cost != 0:
        return None
    edges = set()
    for u in range(N):
        for l in range(d):
            v = int(nbr[l, u])
            edges.add((u, v) if u < v else (v, u))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if best[0] >= moore:
        return best

    while time.monotonic() < deadline:
        if best[0] >= moore:
            break
        k = rng.choice((1, 2, 2, 3, 3, 4))
        lo = best[0] // (2 * k) + 1
        G, MUL = _sample_group(lo, rng)
        if 2 * k * G <= best[0]:
            continue
        INV = _inverse(G, MUL)
        res = _search(d, D, k, G, MUL, INV, rng, deadline, 3000, 800)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
