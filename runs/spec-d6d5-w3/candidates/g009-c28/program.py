import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: random bi-regular bipartite graphs (d disjoint perfect matchings
# between sides A and B of size N), improved by simulated annealing over
# matching swaps. Cost = number of vertex pairs at distance > D, plus a penalty
# for repeated edges. Distances come from dense boolean matrix powers (numpy),
# so each evaluation is a handful of matrix products.
# ----------------------------------------------------------------------------

def _cost(N, perms, D):
    """Bad-pair count at distance > D plus duplicate-edge penalty. Zero means valid."""
    V = 2 * N
    M = np.zeros((V, V), dtype=np.float32)
    idx = np.arange(N)
    for row in perms:
        M[idx, N + row] = 1.0
        M[N + row, idx] = 1.0
    np.fill_diagonal(M, 1.0)
    R = M
    for _ in range(D - 1):
        R = np.minimum(R @ M, 1.0)
    zeros = V * V - int(np.count_nonzero(R))
    S = np.sort(perms, axis=0)
    dups = int(np.count_nonzero(S[1:] == S[:-1]))
    return zeros // 2 + 2 * dups


def _anneal(N, d, D, nprng, rng, deadline):
    """Anneal d permutations of range(N) until cost 0. Returns perms array or None."""
    perms = np.stack([nprng.permutation(N) for _ in range(d)]).astype(np.int64)
    cur = _cost(N, perms, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / span)
        T = 1.5 * (0.1 / 1.5) ** frac
        k = rng.randrange(d)
        a = rng.randrange(N)
        b = rng.randrange(N)
        if a == b:
            continue
        perms[k, a], perms[k, b] = perms[k, b], perms[k, a]
        new = _cost(N, perms, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            perms[k, a], perms[k, b] = perms[k, b], perms[k, a]
    return perms if cur == 0 else None


def _edges_from_perms(N, perms):
    d = perms.shape[0]
    return [(a, N + int(perms[k][a])) for k in range(d) for a in range(N)]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)
    nprng = np.random.default_rng(seed & 0x7FFFFFFF)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    consider(fb_n, fb_e)
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration-style early exit: already at the Moore bound.
    if best[0] == lib.moore_bound(d, D) and lib.is_valid(best[0], best[1], d, D):
        return best[0], best[1]

    # Annealed random bi-regular search above the current best order.
    best_half = best[0] // 2
    stretch = max(1, best_half // 10)
    while time.monotonic() < deadline - 2.0:
        N = max(d, best_half + stretch)
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, 0.3 * remaining))
        perms = _anneal(N, d, D, nprng, rng, slice_end)
        if perms is not None:
            e = _edges_from_perms(N, perms)
            if consider(2 * N, e):
                best_half = N
            # on a rejected candidate the target stays; time is still bounded
        else:
            stretch = max(1, stretch // 2)

    n, e = best[0], best[1]
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
