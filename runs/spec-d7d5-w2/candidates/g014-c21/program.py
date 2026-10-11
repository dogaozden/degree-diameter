import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bit-parallel distance reach over a d-regular bipartite graph.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _reach(nb, n, D):
    """reach[v] is a bitset (uint64 words) of vertices within distance D of v."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for j in range(nb.shape[1]):
            new |= reach[nb[:, j]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _cost(nb, n, D):
    """Number of ordered unreached pairs (0 means diameter <= D)."""
    reach = _reach(nb, n, D)
    return n * n - int(_POP8[reach.view(np.uint8)].sum())


# ----------------------------------------------------------------------------
# 2-switch annealing on bipartite d-regular graphs with h vertices per side.
# NA[a, i] = B-index of a's i-th neighbour, NB[b, j] = A-index of b's j-th neighbour.
# ----------------------------------------------------------------------------

def _apply(NA, NB, a1, i, a2, j, b1, b2):
    """Replace edges a1-b1, a2-b2 by a1-b2, a2-b1 (both sides updated)."""
    s1 = int(np.flatnonzero(NB[b1] == a1)[0])
    s2 = int(np.flatnonzero(NB[b2] == a2)[0])
    NA[a1, i] = b2
    NA[a2, j] = b1
    NB[b1, s1] = a2
    NB[b2, s2] = a1


def _anneal(h, d, D, rng, deadline):
    """Start from a random Haar-type graph, then 2-switch anneal until diameter <= D.

    Returns (n, edges) or None if the deadline passes first.
    """
    if h < d or d < 1:
        return None
    n = 2 * h
    S = rng.sample(range(h), d)
    NA = np.array([[(i + s) % h for s in S] for i in range(h)], dtype=np.int64)
    NB = np.array([[(b - s) % h for s in S] for b in range(h)], dtype=np.int64)

    def nbm():
        return np.ascontiguousarray(np.vstack([NA + h, NB]))

    cost = _cost(nbm(), n, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - start) / span
        T = max(0.2, 2.0 * (1.0 - frac))
        a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = int(NA[a1, i])
        b2 = int(NA[a2, j])
        if b1 == b2 or (NA[a1] == b2).any() or (NA[a2] == b1).any():
            continue
        _apply(NA, NB, a1, i, a2, j, b1, b2)
        c2 = _cost(nbm(), n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(NA, NB, a1, i, a2, j, b2, b1)  # undo
    edges = [(a, h + int(NA[a, j])) for a in range(h) for j in range(d)]
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if d == 2:
            # Even cycle C_{2D}: bipartite, degree 2, diameter D.
            m = 2 * D
            consider(m, [(i, (i + 1) % m) for i in range(m)])
            return best

        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    pn, pe = lib.projective_plane_incidence(q)
                    consider(pn, pe)
                    break
            if lib.is_prime_power(d - 1):
                return best

        # Adaptive ratchet over the side size h (order n = 2h).
        moore = lib.moore_bound(d, D)
        h = max(d, int(0.25 * moore / 2))
        step = max(2, h // 8)
        good_h = None
        attempt_budget = max(2.0, 0.2 * budget)

        while True:
            now = time.monotonic()
            rem = deadline - now
            if rem < 1.0:
                break
            tb = min(rem - 0.5, attempt_budget)
            if tb <= 0.3:
                break
            res = _anneal(h, d, D, rng, now + tb)
            if res is not None:
                consider(res[0], res[1])
                good_h = h if good_h is None else max(good_h, h)
                h += step
            else:
                if good_h is None:
                    h = max(d, h - step)
                else:
                    step = max(1, step // 2)
                    h = good_h + step
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
