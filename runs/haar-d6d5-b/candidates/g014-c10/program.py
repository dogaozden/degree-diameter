"""Bipartite degree-diameter search for d=6, D=5 via edge-switching annealing on random-like regular bipartite graphs.

Instead of searching Haar graphs over groups, this starts from a circulant bipartite graph, scrambles it with
degree-preserving edge switches, and anneals the number of vertex pairs at distance more than D. Every returned
graph is checked with lib.is_valid. If the search fails, a valid Haar fallback or a hypercube is returned.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
TARGET_N = 342  # per side; total order 684 matches the record


# ------------------------------------------------------------------ fast bad-pair counting

_SELF_CACHE = {}


def _self_bits(n):
    """Bitset matrix with row v containing exactly bit v."""
    if n not in _SELF_CACHE:
        W = (n + 63) // 64
        S = np.zeros((n, W), dtype=np.uint64)
        idx = np.arange(n)
        S[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
        _SELF_CACHE[n] = S
    return _SELF_CACHE[n]


def _bad_pairs(nb, n, D):
    """Number of unordered vertex pairs at distance more than D (exact)."""
    reach = _self_bits(n)
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    ones = int(np.unpackbits(reach.view(np.uint8)).sum())
    return (n * n - ones) // 2


# ------------------------------------------------------------------ switching search

def _start(N, d, rng):
    """Simple d-regular bipartite graph: circulant with distinct shifts. Rows 0..N-1 are A, N..2N-1 are B."""
    shifts = rng.choice(N, d, replace=False)
    A = np.arange(N)
    nbA = N + (A[:, None] + shifts[None, :]) % N
    nbB = (A[:, None] - shifts[None, :]) % N
    return np.vstack([nbA, nbB]).astype(np.int64)


def _try_swap(nb, N, d, rng):
    """Degree-preserving switch: a1-b1, a2-b2 become a1-b2, a2-b1. Returns False (no change) if invalid."""
    a1, a2 = (int(v) for v in rng.choice(N, 2, replace=False))
    i = int(rng.integers(d))
    j = int(rng.integers(d))
    b1 = int(nb[a1, i])
    b2 = int(nb[a2, j])
    if (nb[a1] == b2).any() or (nb[a2] == b1).any():
        return False
    nb[a1, i] = b2
    nb[a2, j] = b1
    nb[b1, int(np.argmax(nb[b1] == a1))] = a2
    nb[b2, int(np.argmax(nb[b2] == a2))] = a1
    return True


def _anneal(N, d, D, deadline, rng):
    """Anneal a simple d-regular bipartite graph with 2N vertices toward zero bad pairs."""
    n = 2 * N
    nb = _start(N, d, rng)
    for _ in range(20 * N):
        _try_swap(nb, N, d, rng)
    cost = _bad_pairs(nb, n, D)
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while True:
        if cost == 0:
            return nb
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 1.0 * (1.0 - (now - t0) / span) + 0.15
        old = nb.copy()
        if not _try_swap(nb, N, d, rng):
            continue
        new = _bad_pairs(nb, n, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            nb[:] = old


def _search(d, D, rng, t_end):
    """Climb N from TARGET_N while successful; if TARGET_N fails, try smaller orders. Returns (N, nb) or None."""
    best = None
    N = TARGET_N
    while time.monotonic() < t_end:
        now = time.monotonic()
        nb = _anneal(N, d, D, now + 0.5 * (t_end - now), rng)
        if nb is None:
            break
        best = (N, nb)
        N += 1
    if best is None:
        for N in (336, 330, 320):
            now = time.monotonic()
            if now >= t_end:
                break
            nb = _anneal(N, d, D, now + 0.5 * (t_end - now), rng)
            if nb is not None:
                best = (N, nb)
                break
    return best


# ------------------------------------------------------------------ fallbacks

def _meta_haar(m, k, lam, S):
    """Haar graph of the metacyclic group Z_m x|_lam Z_k with connection set S (element (a, j) = a*k + j)."""
    N = m * k

    def mul(x, y):
        a, b = divmod(x, k)
        c, e = divmod(y, k)
        return ((a + pow(lam, b, m) * c) % m) * k + (b + e) % k

    edges = []
    for s in sorted(set(S)):
        for g in range(N):
            edges.append((g, N + mul(s, g)))
    return 2 * N, edges


def _trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    k = min(d, D)
    if k <= 0:
        return 1, []
    n = 1 << k
    edges = [(x, x | (1 << i)) for x in range(n) for i in range(k) if not (x >> i) & 1]
    return n, edges


# ------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    t0 = time.monotonic()
    t_end = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    found = None
    try:
        found = _search(d, D, rng, t_end)
    except Exception:
        found = None
    if found is not None:
        try:
            N, nb = found
            n = 2 * N
            edges = [(a, int(nb[a, k])) for a in range(N) for k in range(d)]
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    try:
        n, edges = _meta_haar(33, 10, 26, [0, 179, 116, 180, 47, 306])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _trivial(d, D)
