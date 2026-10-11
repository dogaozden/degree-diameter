import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 50 for speed)."""
    for q in range(min(d - 1, 50), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: random bipartite d-regular graphs repaired by simulated
# annealing on layer swaps, with the distance check done on bit-packed
# reachability sets.
#
# Representation: d permutations P[l] of range(N). A-vertex i is joined to
# B-vertex N + P[l][i] in layer l. Each layer swap keeps every vertex at
# degree d, so the graph stays d-regular and bipartite. Duplicate edges across
# layers are penalised so the final graph is simple.
#
# Cost = (ordered vertex pairs at distance > D) + PEN * (duplicate edges).
# The order is searched by growth then bisection over N (total order 2N).
# Every candidate is checked with lib.is_valid before it is kept, and the
# fallback is K_{d,d}.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _swap(P, Q, l, i, i2):
    """Swap the B-targets of A-vertices i and i2 in layer l (self-inverse)."""
    a = P[l, i]
    b = P[l, i2]
    P[l, i] = b
    P[l, i2] = a
    Q[l, b] = i
    Q[l, a] = i2


def _attempt(d, D, N, deadline, rng, nprng):
    """Simulated annealing for a d-regular bipartite graph on 2N vertices with diameter <= D.

    Returns (n, edges) on success, or None if the deadline is reached first.
    """
    V = 2 * N
    W = (V + 63) // 64
    idx = np.arange(V, dtype=np.int64)
    bits = np.left_shift(np.ones(V, dtype=np.uint64), (idx & 63).astype(np.uint64))
    base = np.zeros((V, W), dtype=np.uint64)
    base[idx, idx >> 6] = bits
    fullrow = np.zeros(W, dtype=np.uint64)
    np.bitwise_or.at(fullrow, idx >> 6, bits)

    P = np.empty((d, N), dtype=np.int64)
    Q = np.empty((d, N), dtype=np.int64)
    arN = np.arange(N, dtype=np.int64)
    for l in range(d):
        P[l] = nprng.permutation(N)
        Q[l, P[l]] = arN
    nb = np.empty((d, V), dtype=np.int64)
    PEN = 2 * V

    def reach_of():
        nb[:, :N] = N + P
        nb[:, N:] = Q
        reach = base.copy()
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nb[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        return reach

    def evaluate():
        r = reach_of()
        unreached = V * V - int(_POP16[r.view(np.uint16)].sum())
        dup = d * N - np.unique((arN[None, :] * N + P).ravel()).size
        return unreached + PEN * dup, r

    cost, reach = evaluate()
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        temp = 0.3 + 2.0 * (1.0 - frac)
        l = rng.randrange(d)
        i = None
        if rng.random() < 0.6:
            bad_rows = np.flatnonzero((reach != fullrow).any(axis=1))
            if bad_rows.size:
                u = int(bad_rows[rng.randrange(bad_rows.size)])
                i = u if u < N else int(Q[l, u - N])
        if i is None:
            i = rng.randrange(N)
        i2 = rng.randrange(N)
        if i2 == i:
            continue
        _swap(P, Q, l, i, i2)
        c2, r2 = evaluate()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            _swap(P, Q, l, i, i2)

    edges = [(i, N + int(P[l, i])) for l in range(d) for i in range(N)]
    return V, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1) and d - 1 <= 50:
                return best

    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    # Bisection/growth over N (each side has N vertices; total order 2N).
    mb = lib.moore_bound(d, D)
    lo = d                      # K_{d,d} is known valid
    hi = mb // 2 + 1            # orders beyond this are impossible
    grow = True
    try:
        while time.monotonic() < deadline - 0.5:
            if hi - lo <= 1:
                break
            if grow:
                N = min(hi - 1, int(lo * 1.6) + 1)
            else:
                N = (lo + hi) // 2
            N = max(N, lo + 1)
            now = time.monotonic()
            remaining = deadline - now
            slice_end = min(deadline, now + max(1.5, 0.35 * remaining))
            res = _attempt(d, D, N, slice_end, rng, nprng)
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                lo = N
                consider(res[0], res[1])
            else:
                hi = N
                grow = False
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
