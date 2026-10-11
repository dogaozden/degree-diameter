import math
import random
import time

import numpy as np

import lib


# Bold alternative to the parent's voltage-lift search: a d-regular bipartite
# graph built from d random perfect matchings between two sides A and B of size m.
# Layer l is a permutation sigma_l: A -> B, so a is joined to sigma_l(a) for each l.
# Simulated annealing swaps the images of two A-vertices within one layer, which
# keeps every vertex at degree d, and minimizes the number of ordered vertex pairs
# at distance > D plus a penalty for duplicate edges. A zero-cost result is a
# valid bipartite graph with 2m vertices. The search binary-searches on m.
# Every candidate is checked with lib.is_valid, and the K_{d,d} / projective-plane
# fallbacks are kept, so each case still returns a valid graph.

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PEN = 40  # cost of one duplicate edge


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _nbr_from(sigma, m):
    """Neighbour table of shape (d, 2m): A-vertex a -> m + sigma_l(a); B-vertex m + b -> inverse."""
    d = sigma.shape[0]
    inv = np.empty((d, m), dtype=np.int64)
    rows = np.arange(d)[:, None]
    inv[rows, sigma] = np.arange(m, dtype=np.int64)[None, :]
    nbr = np.empty((d, 2 * m), dtype=np.int64)
    nbr[:, :m] = m + sigma
    nbr[:, m:] = inv
    return nbr


def _cost(sigma, m, D):
    """Ordered unreached pairs within distance D, plus a penalty per duplicate edge. 0 means valid."""
    d = sigma.shape[0]
    N = 2 * m
    nbr = _nbr_from(sigma, m)
    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    unreached = N * N - total
    rs = np.sort(sigma.T, axis=1)
    dup = int(np.count_nonzero(rs[:, 1:] == rs[:, :-1]))
    return unreached + _PEN * dup


def _anneal(d, D, m, rng, deadline):
    """Simulated annealing on the layer permutations. Returns sigma (zero cost) or None."""
    nprng = np.random.default_rng(rng.randrange(1 << 30))
    sigma = np.array([nprng.permutation(m) for _ in range(d)], dtype=np.int64)
    cost = _cost(sigma, m, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - t0) / span
        temp = max(0.5, 2.0 * (1.0 - frac))
        l = rng.randrange(d)
        a1, a2 = rng.sample(range(m), 2)
        sigma[l, a1], sigma[l, a2] = sigma[l, a2], sigma[l, a1]
        c2 = _cost(sigma, m, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            sigma[l, a1], sigma[l, a2] = sigma[l, a2], sigma[l, a1]
    return sigma


def _edges_from(sigma, m):
    d = sigma.shape[0]
    edges = []
    for l in range(d):
        for a in range(m):
            edges.append((a, m + int(sigma[l, a])))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    # Exact constructions for D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: random d-regular bipartite graphs repaired by annealing.
    if d >= 2 and time.monotonic() < deadline:
        moore = lib._moore_bound(d, D)
        m = max(d, best_n // 2 + 1, moore // 8)
        lo, hi = None, None
        while time.monotonic() < deadline:
            if 2 * m > 4000:
                break
            if lo is not None and hi is not None and hi - lo <= 1:
                break
            now = time.monotonic()
            remaining = deadline - now
            slice_end = min(deadline, now + max(2.0, 0.35 * remaining))
            sigma = _anneal(d, D, m, rng, slice_end)
            if sigma is not None:
                consider(2 * m, _edges_from(sigma, m))
                lo = m
                if hi is None:
                    m = m + max(1, m // 20)
                else:
                    m = (lo + hi) // 2
            else:
                hi = m
                if lo is None:
                    m = max(d, m - max(1, m // 20))
                else:
                    m = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
