"""Bipartite d-regular search by 2-switch annealing over random-like lifts.

Family: d-regular bipartite graphs on 2m vertices (left a -> right b). Start from
a Haar graph (circulant with d distinct shifts), then apply degree-preserving
2-switches while annealing the number of vertex pairs at distance > D. Distances
are computed for all sources at once with packed uint64 bitsets in numpy.

Fallbacks: K_{d,d} (optimal for D = 2), the projective-plane incidence graph and
the Araujo-Pardo-Lopez graph for D = 3. Every returned graph passes lib.is_valid.
"""
import math
import random
import time

import numpy as np

import lib


_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _consider(best, cand, d, D):
    """Replace best by cand if cand is larger and passes the exact validity check."""
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def _ident(n):
    """Bitset matrix with row v holding only bit v."""
    W = (n + 63) // 64
    I = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    I[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    return I


def _bad_pairs(n, nb, D, I):
    """Number of unordered vertex pairs at distance > D, for a graph given by neighbour array nb (n x d)."""
    R = I
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nb], axis=1)
    total = int(_POP8[R.view(np.uint8)].sum())
    return (n * n - total) // 2


def _anneal(m, d, D, rng, deadline, T0=1.5, T1=0.05):
    """Anneal a d-regular bipartite graph with m+m vertices to diameter <= D.

    Returns the edge list (valid, simple, bipartite, d-regular) or None.
    """
    n = 2 * m
    E = m * d
    I = _ident(n)
    shifts = rng.sample(range(m), d)
    EA = np.repeat(np.arange(m, dtype=np.int64), d)
    EB = np.array([(a + s) % m for a in range(m) for s in shifts], dtype=np.int64)
    present = {a * m + b for a, b in zip(EA.tolist(), EB.tolist())}

    def nb_now():
        left = EB.reshape(m, d) + m
        order = np.argsort(EB, kind="stable")
        right = EA[order].reshape(m, d)
        return np.concatenate([left, right], axis=0)

    cost = _bad_pairs(n, nb_now(), D, I)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        a1 = e1 // d
        a2 = e2 // d
        if a1 == a2:
            continue
        b1 = int(EB[e1])
        b2 = int(EB[e2])
        if b1 == b2:
            continue
        k1 = a1 * m + b2
        k2 = a2 * m + b1
        if k1 in present or k2 in present:
            continue
        EB[e1] = b2
        EB[e2] = b1
        c2 = _bad_pairs(n, nb_now(), D, I)
        limit = cost - T * math.log(1.0 - rng.random())
        if c2 <= limit:
            present.discard(a1 * m + b1)
            present.discard(a2 * m + b2)
            present.add(k1)
            present.add(k2)
            cost = c2
        else:
            EB[e1] = b1
            EB[e2] = b2
    if cost != 0:
        return None
    return [(a, m + int(EB[a * d + t])) for a in range(m) for t in range(d)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3 * time_limit, time_limit - 4.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, which has diameter 2 and is optimal for D = 2.
    fb = lib.haar_graph(d, range(d))
    best = fb if lib.is_valid(fb[0], fb[1], d, D) else (1, [])
    if D == 2:
        return best

    rng = random.Random(seed * 1000003 + d * 101 + D)

    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            best = _consider(best, (n, e), d, D)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                best = _consider(best, (n, e), d, D)
            except Exception:
                pass

    # Main search: grow m while annealing succeeds; retry the current m otherwise.
    m = max(d + 1, best[0] // 2 + 1)
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(1.0, 0.5 * remaining))
        res = _anneal(m, d, D, rng, slice_end)
        if res is not None:
            best = _consider(best, (2 * m, res), d, D)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return fb
    return best
