import math
import random
import time

import numpy as np

import lib

TIME_FRAC = 0.8     # fraction of time_limit used for search
MARGIN = 2.0        # seconds reserved for final checks and return
N_CAP = 6000        # hard cap on vertex count
MOORE_FRAC = 0.67   # initial guess for the side size, as a fraction of the Moore bound / 2
SLICE_FRAC = 0.3    # share of remaining time given to one annealing attempt


def _reach_bad(nb, n, D):
    """Number of ordered (source, vertex) pairs NOT within distance D. Zero iff valid."""
    d = nb.shape[1]
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        M = R.copy()
        for k in range(d):
            M |= R[:, nb[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return n * n - int(np.count_nonzero(R))


def _try_switch(nb, rng, N):
    """Propose a bipartite double-edge switch on left vertices 0..N-1. Returns None if invalid."""
    d = nb.shape[1]
    a = rng.randrange(N)
    c = rng.randrange(N)
    if a == c:
        return None
    p = rng.randrange(d)
    q = rng.randrange(d)
    b = int(nb[a, p])
    e = int(nb[c, q])
    if b == e:
        return None
    if (nb[a] == e).any() or (nb[c] == b).any():
        return None
    return a, p, b, c, q, e


def _apply(nb, a, p, b, c, q, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b). Caller guarantees the rows are consistent."""
    nb[a, p] = e
    nb[c, q] = b
    rb = np.flatnonzero(nb[b] == a)[0]
    nb[b, rb] = c
    re_ = np.flatnonzero(nb[e] == c)[0]
    nb[e, re_] = a


def _anneal(N, d, D, rng, deadline):
    """Anneal a simple d-regular bipartite graph on 2N vertices toward diameter <= D.

    Start from a random Haar graph (a Z_N bi-Cayley graph), then apply double-edge switches,
    which keep the graph simple, bipartite and d-regular. Returns the neighbour table or None.
    """
    n = 2 * N
    S = rng.sample(range(N), d)
    nb = np.empty((n, d), dtype=np.int64)
    ar = np.arange(N, dtype=np.int64)
    for k, s in enumerate(S):
        nb[:N, k] = N + (ar + s) % N
        nb[N:, k] = (ar - s) % N

    cur = _reach_bad(nb, n, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        T = 3.0 * (1.0 - frac) + 0.05
        mv = _try_switch(nb, rng, N)
        if mv is None:
            continue
        a, p, b, c, q, e = mv
        _apply(nb, a, p, b, c, q, e)
        new = _reach_bad(nb, n, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _apply(nb, a, p, e, c, q, b)  # undo
    return nb


def _search_sizes(d, D, rng, deadline, N_start):
    """Search side sizes N, climbing after success and descending after failure."""
    best = None
    N = N_start
    while time.monotonic() < deadline and N >= d:
        remaining = deadline - time.monotonic()
        slice_t = max(1.0, SLICE_FRAC * remaining)
        nb = _anneal(N, d, D, rng, min(deadline, time.monotonic() + slice_t))
        if nb is not None:
            n = 2 * N
            edges = [(a, int(b)) for a in range(N) for b in nb[a].tolist()]
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                N += 1
                continue
        N -= 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}

    # Moore-extremal projective plane incidence graph for D = 3.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed * 7919 + 31 * d + D)

    moore = lib._moore_bound(d, D)
    N_start = max(d, int(MOORE_FRAC * moore / 2))
    N_start = min(N_start, N_CAP // 2)

    best = None
    try:
        best = _search_sizes(d, D, rng, deadline, N_start)
    except Exception:
        best = None

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
