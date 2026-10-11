import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe families (kept from the parent as calibration and fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# New family: random bipartite d-regular graphs (union of d perfect matchings
# between two sides of size m), repaired by simulated annealing on the number
# of unreached ordered pairs within distance D. Each move swaps the B-targets
# of two A-vertices inside one matching layer, which keeps every layer a
# permutation, so degrees stay exactly d (duplicate edges only lower degree,
# never break validity). Every result is checked with lib.is_valid.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_MAX_SIDE = 2500


def _unreached(nbr, N, D):
    """Number of ordered vertex pairs at distance more than D (bitset BFS in numpy)."""
    d = nbr.shape[0]
    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - total


def _swap(nbr, P, m, l, i, j):
    """Swap the B-targets of A-vertices i and j in layer l. Applying it twice is the identity."""
    a = int(P[l, i])
    b = int(P[l, j])
    P[l, i] = b
    P[l, j] = a
    nbr[l, i] = m + b
    nbr[l, j] = m + a
    nbr[l, m + a] = j
    nbr[l, m + b] = i


def _anneal(d, D, m, rng, deadline):
    """Anneal a random bipartite d-regular graph with sides of size m. Return nbr or None."""
    N = 2 * m
    P = np.array([rng.sample(range(m), m) for _ in range(d)], dtype=np.int64)
    nbr = np.empty((d, N), dtype=np.int64)
    ar = np.arange(m, dtype=np.int64)
    for l in range(d):
        nbr[l, :m] = m + P[l]
        nbr[l, m + P[l]] = ar
    cost = _unreached(nbr, N, D)
    if cost == 0:
        return nbr
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    t_hi = max(2.0, 0.05 * cost)
    t_lo = 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = t_hi * (t_lo / t_hi) ** min(1.0, (now - t0) / span)
        l = rng.randrange(d)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        _swap(nbr, P, m, l, i, j)
        c2 = _unreached(nbr, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            _swap(nbr, P, m, l, i, j)
    return nbr if cost == 0 else None


def _try(d, D, m, rng, deadline):
    """One annealing attempt at side size m. Return (n, edges) or None."""
    nbr = _anneal(d, D, m, rng, deadline)
    if nbr is None:
        return None
    edges = {(i, int(nbr[l, i])) for l in range(d) for i in range(m)}
    return 2 * m, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # K_{d,d} is optimal for D = 2 (bipartite), so return it at once.
    if D == 2:
        return best

    # Even cycle C_{2D}: degree 2, diameter D, bipartite.
    if d == 2:
        L = 2 * D
        consider(L, [(i, (i + 1) % L) for i in range(L)])
        return best

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: grow the side size m of a random bipartite d-regular graph.
    cap = min(lib.moore_bound(d, D) // 2, _MAX_SIDE)
    lo = max(d, best_n // 2)
    step = max(1, lo // 10)

    while time.monotonic() < deadline and lo < cap:
        cand = min(lo + step, cap)
        now = time.monotonic()
        remaining = deadline - now
        att_deadline = min(deadline, now + max(1.0, 0.35 * remaining))
        res = _try(d, D, cand, rng, att_deadline)
        if res is not None and consider(res[0], res[1]):
            lo = cand
            step = int(step * 1.7) + 1
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
