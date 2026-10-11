"""Bold variant: multi-base voltage lifts over semidirect products, searched with a
vectorized numpy cost function. Replaces the pure-Python bi-Cayley climb with
annealing over k-base (k = 1..4) lifts, where the cost counts unreached pairs
from one representative per base vertex. Left translation is an automorphism of
such lifts, so these representatives suffice.

For D = 3 the projective plane incidence graph is kept as a baseline. The
arc-extension construction is dropped to keep this version focused on the
D >= 4 family. Every result is checked with lib.is_valid before it is kept, and
the K_{d,d} fallback always remains.
"""
import math
import random
import time

import numpy as np

import lib

BIG = 10 ** 6
_MT_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    """MT[g, s] = g * s in Z_m x|_r Z_k, cached as a numpy array."""
    key = (m, k, r)
    t = _MT_CACHE.get(key)
    if t is None:
        order, mul, _ = lib.semidirect_group(m, k, r)
        t = np.array([[mul(g, s) for s in range(order)] for g in range(order)],
                     dtype=np.int64)
        if len(_MT_CACHE) > 64:
            _MT_CACHE.clear()
        _MT_CACHE[key] = t
    return t


def _build_nb(k, G, d, P, S, MT, ar):
    """Neighbour array (2kG x d). Layer L joins A_{i,g} to B_{P[L][i], g * S[L][i]}."""
    nb = np.empty((2 * k * G, d), dtype=np.int64)
    for L in range(d):
        for i in range(k):
            j = P[L][i]
            s = S[L][i]
            a = i * G + ar
            b = (k + j) * G + MT[:, s]
            nb[a, L] = b
            nb[b, L] = a
    return nb


def _cost(nb, k, G, D):
    """Unreached (representative, vertex) pairs within distance D; 0 means valid."""
    N2 = nb.shape[0]
    srt = np.sort(nb, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    if dup:
        return BIG + dup
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = np.zeros(N2, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nbr = nb[fr].ravel()
            nbr = nbr[~seen[nbr]]
            if nbr.size == 0:
                break
            nbr = np.unique(nbr)
            seen[nbr] = True
            fr = nbr
        total += N2 - int(seen.sum())
    return total


def _anneal(d, D, k, G, MT, rng, deadline):
    """Time-scheduled annealing over voltages and layer assignments. Returns nb or None."""
    ar = np.arange(G, dtype=np.int64)
    P = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = _build_nb(k, G, d, P, S, MT, ar)
    cost = _cost(nb, k, G, D)
    if cost == 0:
        return nb
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, min(20.0, 0.1 * cost))
    T_end = 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T_end / T0) ** min(1.0, (now - t0) / span)
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.75:
            i = rng.randrange(k)
            old = S[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[L][i] = new
            nb2 = _build_nb(k, G, d, P, S, MT, ar)
            c2 = _cost(nb2, k, G, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost, nb = c2, nb2
            else:
                S[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            nb2 = _build_nb(k, G, d, P, S, MT, ar)
            c2 = _cost(nb2, k, G, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost, nb = c2, nb2
            else:
                P[L][a], P[L][b] = P[L][b], P[L][a]
    return nb if cost == 0 else None


def _edges_from(nb, k, G):
    """Convert a neighbour array into (n, edges)."""
    A = k * G
    lst = nb.tolist()
    E = []
    for a in range(A):
        for b in lst[a]:
            E.append((a, b))
    return 2 * A, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and n <= moore and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2 and D >= 3:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: multi-base lifts over semidirect products.
    while time.monotonic() < deadline and best[0] < moore:
        n_best = best[0]
        ks = [k for k in (1, 2, 3, 4) if 2 * k * (n_best // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        lo = n_best // (2 * k) + 1
        G = lo + rng.randrange(3)
        if 2 * k * G > moore:
            G = lo
        groups = _groups(G)
        if not groups:
            continue
        rng.shuffle(groups)
        for m, k2, r in groups[:4]:
            now = time.monotonic()
            if now >= deadline:
                break
            remaining = deadline - now
            slice_end = now + max(1.0, min(6.0, remaining / 3.0))
            MT = _mul_table(m, k2, r)
            nb = _anneal(d, D, k, G, MT, rng, min(deadline, slice_end))
            if nb is not None:
                n, e = _edges_from(nb, k, G)
                consider(n, e)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
