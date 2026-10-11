import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: simulated annealing over double-edge swaps on bipartite
# d-regular graphs. Vertices A = 0..h-1, B = h..2h-1. Every swap keeps the
# graph d-regular and bipartite. The cost is the number of ordered vertex pairs
# at distance greater than D, computed with packed-bit reachability sets.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _cost(nbr, base, n, d, D):
    """Number of ordered pairs not within distance D (0 means diameter <= D)."""
    R = base.copy()
    for _ in range(D):
        N2 = R.copy()
        for j in range(d):
            N2 |= R[nbr[:, j]]
        if np.array_equal(N2, R):
            break
        R = N2
    return n * n - int(_POP8[R].sum())


def _anneal(h, d, D, rng, deadline):
    """Anneal from a random circulant bipartite graph on 2h vertices. Returns (n, edges) or None."""
    n = 2 * h
    E = h * d
    shifts = rng.sample(range(h), d)
    nbr = np.empty((n, d), dtype=np.int64)
    idx = np.arange(h, dtype=np.int64)
    for j, s in enumerate(shifts):
        nbr[:h, j] = h + (idx + s) % h
        nbr[h:, j] = (idx - s) % h
    ea = np.repeat(idx, d)
    eb = nbr[:h].reshape(-1).copy()
    ea = ea.tolist()
    eb = eb.tolist()

    M = np.zeros((n, n), dtype=bool)
    ea_np = np.array(ea, dtype=np.int64)
    eb_np = np.array(eb, dtype=np.int64)
    M[ea_np, eb_np] = True
    M[eb_np, ea_np] = True

    v = np.arange(n, dtype=np.int64)
    base = np.zeros((n, (n + 7) // 8), dtype=np.uint8)
    base[v, v >> 3] = np.left_shift(1, v & 7).astype(np.uint8)

    def rep(vert, old, new):
        row = nbr[vert]
        j = int(np.flatnonzero(row == old)[0])
        row[j] = new

    def flip(e1, e2):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Calling again on the result reverts it."""
        a1, b1 = ea[e1], eb[e1]
        a2, b2 = ea[e2], eb[e2]
        M[a1, b1] = False
        M[b1, a1] = False
        M[a2, b2] = False
        M[b2, a2] = False
        M[a1, b2] = True
        M[b2, a1] = True
        M[a2, b1] = True
        M[b1, a2] = True
        rep(a1, b1, b2)
        rep(b1, a1, a2)
        rep(a2, b2, b1)
        rep(b2, a2, a1)
        ea[e1], eb[e1] = a1, b2
        ea[e2], eb[e2] = a2, b1

    cost = _cost(nbr, base, n, d, D)
    t_start = time.monotonic()
    total = max(deadline - t_start, 1e-3)
    T0 = 4.0
    it = 0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        it += 1
        frac = (now - t_start) / total
        T = T0 * (0.05 ** frac)
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        a1, b1 = ea[e1], eb[e1]
        a2, b2 = ea[e2], eb[e2]
        if a1 == a2 or b1 == b2 or M[a1, b2] or M[a2, b1]:
            continue
        flip(e1, e2)
        c2 = _cost(nbr, base, n, d, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            flip(e1, e2)

    if cost != 0:
        return None
    edges = [(int(ea[e]), int(eb[e])) for e in range(E)]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d (Moore-optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    h = max(d, int(0.36 * moore) // 2)

    while time.monotonic() < deadline - 1.0:
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + min(12.0, remaining)
        res = _anneal(h, d, D, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])
            h = max(d, best_n // 2 + 1)
        else:
            h = max(d, best_n // 2 + 1, h - 3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
