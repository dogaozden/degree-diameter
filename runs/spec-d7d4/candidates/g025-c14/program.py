import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Haar-graph search. The bipartite Haar graph H(Z_m, S) has parts a_i, b_j with
# a_i ~ b_{i+s} for s in S. It is d-regular for |S| = d, and it has an automorphism
# swapping the two sides, so the diameter is at most D exactly when:
#   (a) every element of Z_m is reached from 0 by alternating walks of even length
#       <= 2*floor(D/2), where each double step adds an element of S - S;
#   (b) every element of Z_m is reached by walks of odd length <= D from a_0,
#       which means (S-S)-sums followed by one step of +S, or just S.
# Annealing over S (with 0 in S, WLOG by translation) drives the uncovered count to 0.
# ----------------------------------------------------------------------------

def _sumset_idx(X, E, m):
    """Return the sorted distinct residues X + E (mod m), as an index array."""
    vals = (X[:, None] + E[None, :]) % m
    return np.unique(vals.ravel())


def _cost(m, S, D):
    """Number of uncovered a-residues plus uncovered b-residues (0 means diameter <= D)."""
    E = np.array(sorted({(s - t) % m for s in S for t in S}), dtype=np.int64)
    Sa = np.array(S, dtype=np.int64)
    levels = [np.array([0], dtype=np.int64)]
    for _ in range(D // 2):
        levels.append(_sumset_idx(levels[-1], E, m))
    a_mask = np.zeros(m, dtype=bool)
    for X in levels:
        a_mask[X] = True
    b_mask = np.zeros(m, dtype=bool)
    for k in range((D - 1) // 2 + 1):
        b_mask[_sumset_idx(levels[k], Sa, m)] = True
    return (m - int(a_mask.sum())) + (m - int(b_mask.sum()))


def _search(m, d, D, deadline, rng):
    """Anneal a connection set S of size d in Z_m until the Haar graph has diameter <= D."""
    if m < d:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _cost(m, S, D)
    T = 1.5
    best_seen = cur
    stall = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, d)
        v = rng.randrange(1, m)
        if v in S:
            continue
        S2 = S[:]
        S2[i] = v
        c2 = _cost(m, S2, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = S2, c2
        T = max(0.15, T * 0.9995)
        if cur < best_seen:
            best_seen = cur
            stall = 0
        else:
            stall += 1
            if stall > 4000:  # reheat when stuck
                T = 1.0
                stall = 0
                best_seen = cur
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (Haar graph with S = all of Z_d), diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    rng = random.Random(seed)
    deadline_total = start + 0.80 * time_limit

    lo = d                      # known feasible
    hi = max(d, lib._moore_bound(d, D) // 2)
    best_m, best_S = d, None

    while lo < hi and time.monotonic() < deadline_total:
        mid = (lo + hi + 1) // 2
        remaining = deadline_total - time.monotonic()
        slice_len = min(max(0.5, remaining * 0.35), remaining)
        S = _search(mid, d, D, time.monotonic() + slice_len, rng)
        ok = False
        if S is not None:
            n, e = lib.haar_graph(mid, S)
            if lib.is_valid(n, e, d, D):
                ok = True
                if n > best[0]:
                    best = (n, e)
                best_m, best_S = mid, S
        if ok:
            lo = mid
        else:
            hi = mid - 1

    # Spend leftover time trying to extend the largest feasible m by one step.
    while best_S is not None and time.monotonic() < deadline_total:
        m_try = best_m + 1
        remaining = deadline_total - time.monotonic()
        if remaining <= 0.2:
            break
        S = _search(m_try, d, D, time.monotonic() + remaining, rng)
        if S is None:
            break
        n, e = lib.haar_graph(m_try, S)
        if not lib.is_valid(n, e, d, D):
            break
        best_m, best_S = m_try, S
        if n > best[0]:
            best = (n, e)

    return best
