import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact family: projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: annealed random d-regular bipartite graphs.
#
# Instead of algebraic lifts, start from a circulant d-regular bipartite graph
# on two sides of size s, scramble it with double-edge swaps (which keep every
# degree equal to d, keep the graph bipartite and keep it simple), and then
# anneal the number of unordered vertex pairs at distance > D. Reachability is
# tracked with packed uint64 bitsets so each cost evaluation is a few numpy ops.
# Growing s gives a larger order; every returned graph is re-checked with
# lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _reach_bits(n, NB, D):
    """Packed reachability: row v has bit u set when u is within distance D of v."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for t in range(NB.shape[1]):
            new |= reach[NB[:, t]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _bad_pairs(n, NB, D):
    """Number of unordered vertex pairs at distance greater than D."""
    reach = _reach_bits(n, NB, D)
    bits = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - bits) // 2


def _swap_ok(Ea, Eb, eset, s, i, j):
    """Check that the double-edge swap on edges i and j keeps the graph simple."""
    a1, b1 = Ea[i], Eb[i]
    a2, b2 = Ea[j], Eb[j]
    if a1 == a2 or b1 == b2:
        return False
    return (a1 * s + b2) not in eset and (a2 * s + b1) not in eset


def _apply(NB, Ea, Eb, eset, s, i, j):
    """Swap edges (a1,b1),(a2,b2) into (a1,b2),(a2,b1). Applying it again on (i, j) reverts it."""
    a1, b1 = Ea[i], Eb[i]
    a2, b2 = Ea[j], Eb[j]
    B1, B2 = s + b1, s + b2

    r = NB[a1]
    r[np.flatnonzero(r == B1)[0]] = B2
    r = NB[a2]
    r[np.flatnonzero(r == B2)[0]] = B1
    r = NB[B1]
    r[np.flatnonzero(r == a1)[0]] = a2
    r = NB[B2]
    r[np.flatnonzero(r == a2)[0]] = a1

    eset.discard(a1 * s + b1)
    eset.discard(a2 * s + b2)
    eset.add(a1 * s + b2)
    eset.add(a2 * s + b1)
    Eb[i] = b2
    Eb[j] = b1


def _anneal(s, d, D, rng, deadline):
    """Try to find a d-regular bipartite graph with sides of size s and diameter <= D.

    Returns (n, edges) or None if the deadline is reached first.
    """
    n = 2 * s
    m = s * d
    NB = np.empty((n, d), dtype=np.int64)
    Ea = [0] * m
    Eb = [0] * m
    eset = set()
    for a in range(s):
        for t in range(d):
            b = (a + t) % s
            NB[a, t] = s + b
            NB[s + b, t] = (b - t) % s
            Ea[a * d + t] = a
            Eb[a * d + t] = b
            eset.add(a * s + b)

    # Scramble with random double-edge swaps.
    for _ in range(3 * m):
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i != j and _swap_ok(Ea, Eb, eset, s, i, j):
            _apply(NB, Ea, Eb, eset, s, i, j)

    cost = _bad_pairs(n, NB, D)
    if cost == 0:
        return n, [(Ea[k], s + Eb[k]) for k in range(m)]

    c0 = max(1.0, float(cost))
    T0 = max(1.0, 0.02 * c0)
    Tend = 0.3
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (Tend / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j or not _swap_ok(Ea, Eb, eset, s, i, j):
            continue
        _apply(NB, Ea, Eb, eset, s, i, j)
        new = _bad_pairs(n, NB, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            _apply(NB, Ea, Eb, eset, s, i, j)

    return n, [(Ea[k], s + Eb[k]) for k in range(m)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact projective-plane incidence graph (diameter 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    rng = random.Random(seed)
    s = max(d, best_n // 2)
    step = max(1, s // 8)
    s_ok = None

    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        attempt_deadline = min(deadline, now + max(2.0, 0.35 * remaining))
        res = _anneal(s, d, D, rng, attempt_deadline)
        if res is not None:
            consider(res[0], res[1])
            s_ok = s
            s = s + step
        else:
            step = max(1, step // 2)
            if s_ok is not None:
                s = s_ok + step
            else:
                s = max(d, s - step)

    return best
