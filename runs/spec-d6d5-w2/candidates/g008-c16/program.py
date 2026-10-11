"""Bi-Cayley voltage-lift search with a numpy diameter checker, plus PG/Araujo-Lopez baselines.

Lifts are built over semidirect products Z_m x| Z_k2 with k base vertices per side.
Each lift is checked by BFS from one representative per base vertex (vertex-transitive
within each base vertex), annealed over voltages and B-assignments, and then confirmed
with lib.is_valid. Every returned graph is verified; the fallback is K_{d,d}.
"""
import math
import random
import time

import numpy as np

import lib

BIG = 10 ** 9


def _deadline(start, time_limit):
    return start + max(0.5, min(0.8 * time_limit, time_limit - 5.0))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G (k2 small), returned as (order, mul)."""
    small = [k2 for k2 in range(1, min(G, 12) + 1) if G % k2 == 0 and G // k2 >= 2]
    if not small:
        return None
    for _ in range(10):
        k2 = rng.choice(small)
        m = G // k2
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not rs:
            continue
        r = rng.choice(rs)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, d, D, darts, perms):
    """Unreached (representative, vertex) pairs within distance D. Zero iff the lift has diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    N = 2 * k * G
    g = np.arange(G, dtype=np.int64)
    src, dst = [], []
    for (i, j, _s), p in zip(darts, perms):
        src.append(i * G + g)
        dst.append((k + j) * G + p)
    a = np.concatenate(src)
    b = np.concatenate(dst)
    U = np.concatenate([a, b])
    V = np.concatenate([b, a])
    order = np.argsort(U, kind="stable")
    nb = V[order].reshape(N, d)  # every vertex has exactly d neighbours

    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for s0 in reps:
        vis = np.zeros(N, dtype=bool)
        vis[s0] = True
        front = np.array([s0], dtype=np.int64)
        for _ in range(D):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~vis[nxt]])
            if nxt.size == 0:
                break
            vis[nxt] = True
            front = nxt
        total += N - int(vis.sum())
    return total


def _edges(k, G, darts, perms):
    E = []
    for (i, j, _s), p in zip(darts, perms):
        for x in range(G):
            E.append((i * G + x, (k + j) * G + int(p[x])))
    return 2 * k * G, E


def _search_group(k, G, d, D, mul, rng, deadline, iters):
    """Anneal voltages and B-assignments for one group. Returns (0, darts, perms) on success."""
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = np.array([mul(x, s) for x in range(G)], dtype=np.int64)
            cache[s] = p
        return p

    P = [rng.sample(range(k), k) for _ in range(d)]
    V = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def darts():
        return [(i, P[L][i], V[L][i]) for L in range(d) for i in range(k)]

    def evaluate(ds):
        return _cost(k, G, d, D, ds, [perm(s) for _, _, s in ds])

    cur = evaluate(darts())
    T = 1.5
    it = 0
    while cur > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        T = max(0.15, T * 0.997)
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = V[L][i]
            V[L][i] = rng.randrange(G)
            new = evaluate(darts())
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                V[L][i] = old
        else:
            i1, i2 = rng.sample(range(k), 2)
            P[L][i1], P[L][i2] = P[L][i2], P[L][i1]
            new = evaluate(darts())
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                P[L][i1], P[L][i2] = P[L][i2], P[L][i1]
    if cur == 0:
        ds = darts()
        return 0, ds, [perm(s) for _, _, s in ds]
    return cur, None, None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = _deadline(start, time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    bound = lib.moore_bound(d, D)
    if best[0] >= bound or D <= 2:
        return best[0], best[1]

    # Main search: annealed bi-Cayley lifts over semidirect products.
    try:
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            floor_n = max(best[0], 624) if rng.random() < 0.7 else best[0]
            lo = max(2, (floor_n + 2) // (2 * k))
            hi = lo + max(3, lo // 15)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            cost, ds, perms = _search_group(k, order, d, D, mul, rng, deadline, 1200)
            if ds is None:
                continue
            n, e = _edges(k, order, ds, perms)
            consider(n, e)
            if best[0] >= bound:
                break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0], best[1]
