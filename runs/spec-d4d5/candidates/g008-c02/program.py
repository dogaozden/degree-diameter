import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Degree-preserving bipartite double-edge-swap annealing.
#
# New in this version: instead of group voltage lifts, search directly over
# d-regular bipartite graphs on N + N vertices. A move swaps the B-endpoints of
# two edges (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). This keeps every degree equal to
# d and keeps the graph bipartite. The cost is the number of ordered vertex pairs
# at distance > D, computed by repeated boolean matrix products on a dense
# adjacency matrix that is updated incrementally after each swap.
# ----------------------------------------------------------------------------

def _random_regular_bip(N, d, rng):
    """Random d-regular bipartite graph on N+N vertices as parallel lists (ea, eb), or None."""
    ea, eb, pairs = [], [], set()
    for _ in range(d):
        ok = False
        for _try in range(2000):
            p = list(range(N))
            rng.shuffle(p)
            if all((a, p[a]) not in pairs for a in range(N)):
                ok = True
                break
        if not ok:
            return None
        for a in range(N):
            ea.append(a)
            eb.append(p[a])
            pairs.add((a, p[a]))
    return ea, eb


def _set(A, N, a, b, v):
    A[a, N + b] = v
    A[N + b, a] = v


def _bad(A, M, D):
    """Number of ordered vertex pairs at distance > D (zero means diameter <= D)."""
    R = np.eye(M, dtype=np.float32)
    for _ in range(D):
        R = ((R + R @ A) > 0).astype(np.float32)
    return M * M - int(np.count_nonzero(R))


def _anneal_bip(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on N+N vertices toward diameter <= D; (ea, eb) or None."""
    init = _random_regular_bip(N, d, rng)
    if init is None:
        return None
    ea, eb = init
    M = 2 * N
    E = len(ea)
    pairs = set(zip(ea, eb))
    A = np.zeros((M, M), dtype=np.float32)
    for a, b in zip(ea, eb):
        _set(A, N, a, b, 1)
    cost = _bad(A, M, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        # Geometric cooling in wall-clock time.
        T = 3.0 * (0.3 / 3.0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(E)
        j = rng.randrange(E)
        if i == j:
            continue
        a1, b1, a2, b2 = ea[i], eb[i], ea[j], eb[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in pairs or (a2, b1) in pairs:
            continue
        _set(A, N, a1, b1, 0)
        _set(A, N, a2, b2, 0)
        _set(A, N, a1, b2, 1)
        _set(A, N, a2, b1, 1)
        new = _bad(A, M, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            pairs.discard((a1, b1))
            pairs.discard((a2, b2))
            pairs.add((a1, b2))
            pairs.add((a2, b1))
            ea[i], eb[i] = a1, b2
            ea[j], eb[j] = a2, b1
            cost = new
        else:
            _set(A, N, a1, b2, 0)
            _set(A, N, a2, b1, 0)
            _set(A, N, a1, b1, 1)
            _set(A, N, a2, b2, 1)
    if cost == 0:
        return ea, eb
    return None


# ----------------------------------------------------------------------------
# Known-construction fallbacks (calibration and small D).
# ----------------------------------------------------------------------------

def _pg_if_possible(d):
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo_if_possible(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except ValueError:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    found_search = False

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_if_possible(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo_if_possible(d)
            if ar is not None:
                consider(ar[0], ar[1])

    # Main search: annealed d-regular bipartite graphs with an increasing side size N.
    if d >= 3 and D >= 3:
        N = max(d + 1, best_n // 2 + 1)
        while time.monotonic() < deadline:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.2:
                break
            sub_deadline = now + remaining * 0.6
            res = _anneal_bip(N, d, D, rng, sub_deadline)
            if res is not None:
                ea, eb = res
                edges = [(a, N + b) for a, b in zip(ea, eb)]
                before = best_n
                consider(2 * N, edges)
                if best_n > before:
                    found_search = True
                N += 1
            else:
                if found_search:
                    break
                N -= 1
                if N < d + 1:
                    break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
